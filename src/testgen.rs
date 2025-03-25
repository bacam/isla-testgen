// BSD 2-Clause License
//
// Copyright (c) 2020, 2021, 2022 Brian Campbell
// Copyright (c) 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use rand::Rng;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::File;
use std::num::ParseIntError;
use std::ops::Range;
use std::process::exit;

// TODO: allow B64 or B129
use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::executor::{Frame, StopAction, StopConditions};
use isla_lib::ir::*;
use isla_lib::memory::{Address, Memory};
use isla_lib::simplify::write_events;
use isla_lib::smt::{Checkpoint, Event, Sym};

use isla_testgen::acl2_insts;
use isla_testgen::acl2_insts_parser;
use isla_testgen::asl_tag_files;
use isla_testgen::execution::*;
use isla_testgen::extract_state;
use isla_testgen::generate_testfile;
use isla_testgen::target;
use isla_testgen::target::Target;

use isla::opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

// TODO: to use masks with x86 we'd need to change the type of the masks
// (also in execition::setup_opcode)
fn parse_instruction_masks(little_endian: bool, args: &[String]) -> Vec<(&str, Option<u32>)> {
    let mut iter = args.iter().peekable();
    let mut v: Vec<(&str, Option<u32>)> = vec![];
    loop {
        let s = match iter.next() {
            None => break,
            Some(s) => s,
        };
        let p = iter.peek().copied();
        let m: Option<u32> = match p {
            None => None,
            Some(s) => {
                if s.starts_with("mask:") {
                    iter.next();
                    match u32::from_str_radix(&s[5..], 16) {
                        Ok(m) => Some(if little_endian { u32::from_le(m) } else { u32::from_be(m) }),
                        Err(e) => {
                            eprintln!("Could not parse mask: {}", e);
                            exit(1)
                        }
                    }
                } else {
                    None
                }
            }
        };
        v.push((s, m));
    }
    v
}

enum Encodings<'a, B:BV> {
    ASL(asl_tag_files::Encodings),
    ACL2(Vec<acl2_insts::Instr<'a, B>>),
}

fn instruction_opcode<B: BV>(
    little_endian: bool,
    encodings: &Encodings<B>,
    isa_config: &ISAConfig<B>,
    instruction: &str,
    register_bias: bool,
) -> (B, bool, String) {
    let (opcode, random, description) = if instruction == "_" {
        use Encodings::*;
        let (opcode, description) =
            match encodings {
                ASL(encodings) => {
                    let (op,d) = encodings.random(asl_tag_files::Encoding::A64, register_bias);
                    (B::from_u32(op), d)
                }
                ACL2(encodings) => acl2_insts::sample(encodings),
            };
        println!("Instruction {:#010x}: {}", opcode, description);
        (opcode, true, description)
    } else if instruction.starts_with("0x") {
        println!("Instruction {}", instruction);
        let (opcode_str, description) =
            match instruction.find(' ') {
                None => (instruction, instruction),
                Some(i) => (&instruction[..i], &instruction[i+1..]),
            };
        match B::from_str(opcode_str) {
            Some(opcode) => (opcode, false, description.to_string()),
            None => {
                eprintln!("Could not parse instruction: {}", opcode_str);
                exit(1)
            }
        }
    } else {
        println!("Instruction {}", instruction);
        match assemble_instruction(&instruction, &isa_config) {
            Ok(mut bytes) => {
                bytes.reverse();
                (B::from_bytes(&bytes), false, instruction.to_string())
            }
            Err(msg) => {
                eprintln!("Could not assemble instruction: {}", msg);
                exit(1);
            }
        }
    };
    // TODO: reintroduce big endian or eliminate everywhere
    assert!(little_endian);
    (opcode, random, description)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt("", "max-retries", "Stop if this many instructions in a row are useless", "<retries>");
    opts.optopt("a", "target-arch", "target architecture", "aarch64/morello/morello-aarch64/morello-el3/x86");
    opts.optopt("e", "endianness", "instruction encoding endianness (little default)", "big/little");
    opts.optmulti("t", "tag-file", "parse instruction encodings from tag file", "<file>");
    opts.optopt("", "acl2-insts", "parse instruction encodings in ACL2 format", "<file>");
    opts.optopt("o", "output", "base name for output files", "<file>");
    opts.optopt("n", "number-gens", "number of tests to generate", "<number>");
    opts.optmulti("", "exclude", "exclude matching instructions from tag file", "<regexp>");
    opts.optmulti("k", "kill-at", "stop executions early if they reach this function (with optional context)", "<function name[, function name]>");
    opts.optflag("", "events", "dump final events");
    opts.optflag("", "all-events", "dump events for every behaviour");
    opts.optflag("", "uniform-registers", "Choose from registers uniformly, rather than with a bias");
    opts.optopt("", "z3-timeout", "Soft timeout for Z3 solver (60s default)", "<milliseconds>");
    opts.optopt("", "assertion-reports", "Write backtraces and events for failed assertions", "<file>");
    opts.optflag("", "translation-in-symbolic-execution", "Turn on the MMU with a simple translation table during symbolic execution");
    opts.optmulti("x", "exceptions-at", "Allow processor exceptions at given instruction", "<instruction number>");
    opts.optopt("", "all-paths-for", "Generate tests using all feasible paths for the given instruction", "<instruction number>");
    opts.optflag("", "test-file", "Generate a text test file rather than an object file");
    opts.optmulti("", "memory-region", "Add a memory region (overriding the default)", "<start[-end]>");
    opts.optopt("", "code-region", "Specify the region of memory to be used for code", "<start[-end]>");
    opts.optflag("", "sparse", "Omit untouched initial memory in test");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);

    isla_lib::smt::global_set_param_value("timeout", matches.opt_str("z3-timeout").as_deref().unwrap_or("60000"));

    let translation_in_symbolic_execution = matches.opt_present("translation-in-symbolic-execution");

    use crate::target::MorelloStyle::*;
    use crate::target::X86Style;

    match matches.opt_str("target-arch").as_deref().unwrap_or("aarch64") {
        "aarch64" => {
            if translation_in_symbolic_execution {
                eprintln!("translation-in-symbolic-execution not implemented for plain Aarch64");
                1
            } else {
                testgen_main(target::Aarch64 {}, hasher, opts, matches, arch)
            }
        }
        "morello" => testgen_main(target::Morello { style: EL0, translation_in_symbolic_execution }, hasher, opts, matches, arch),
        "morello-el3" => testgen_main(target::Morello { style: EL3Only, translation_in_symbolic_execution }, hasher, opts, matches, arch),
        "morello-aarch64" => testgen_main(target::Morello { style: AArch64Compatible, translation_in_symbolic_execution }, hasher, opts, matches, arch),
        "x86" => testgen_main(target::X86 { style: X86Style::Plain }, hasher, opts, matches, arch),
        "c86" => testgen_main(target::X86 { style: X86Style::Cap }, hasher, opts, matches, arch),
        "cheriot" => testgen_main(target::CHERIoT {}, hasher, opts, matches, arch),
        target_str => {
            eprintln!("Unknown target architecture: {}", target_str);
            1
        }
    }
}

fn u64_parse(s: &str) -> Result<u64,ParseIntError> {
    if s.len() > 2 && &s[0..2] == "0x" {
        u64::from_str_radix(&s[2..], 16)
    } else {
        u64::from_str_radix(s, 10)
    }
}

fn range_parse(s: &str) -> Range<u64> {
    match s.find('-') {
        Some(i) => u64_parse(&s[..i]).expect("Bad region start")..
            u64_parse(&s[i+1..]).expect("Bad region end"),
        None => {
            let start = u64_parse(s).expect("Bad region start");
            start..start+0x1000
        }
    }
}

fn testgen_main<T: Target, B: BV>(
    target: T,
    mut hasher: Sha256,
    opts: getopts::Options,
    matches: getopts::Matches,
    arch: opts::Architecture<B>,
) -> i32 {
    // TODO: use source_path
    let CommonOpts { num_threads, mut arch, symtab, isa_config, type_info, source_path: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let max_retries = matches.opt_get_default("max-retries", 10).expect("Bad max-retries argument");
    let number_gens = matches.opt_get_default("number-gens", 1).expect("Bad number-gens argument");

    let exclusions = matches.opt_strs("exclude");

    let tag_files = matches.opt_strs("tag-file");
    let acl2_file = matches.opt_str("acl2-insts");
    let encodings =
        if let Some(file_name) = acl2_file {
            let file = File::open(&file_name).unwrap_or_else(|err| panic!("Unable to open tag file {}: {}", file_name, err));
            let input = std::io::read_to_string(file).unwrap();
            let sexp = acl2_insts_parser::SexpParser::new().parse(Box::leak(Box::new(input))).unwrap();
            let instrs = acl2_insts::parse_instrs::<B>(Box::leak(Box::new(sexp))).unwrap();
            Encodings::ACL2(instrs)
        } else {
            let encodings = if tag_files.is_empty() {
                asl_tag_files::Encodings::default()
            } else {
                asl_tag_files::read_tag_files(&tag_files, &exclusions)
            };
            Encodings::ASL(encodings)
        };

    let register_types: HashMap<Name, Ty<Name>> = arch
        .iter()
        .filter_map(|d| match d {
            Def::Register(reg, ty, _) => Some((*reg, ty.clone())),
            _ => None,
        })
        .collect();

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut arch, symtab, type_info, &isa_config, AssertionMode::Optimistic, true);

    let regions = matches.opt_strs("memory-region");
    let symbolic_regions: Vec<Range<u64>> =
        if regions.is_empty() {
            vec![0x1000..0x2000]
        } else {
            regions.iter().map(|s| range_parse(&s)).collect()
        };
    let symbolic_code_regions =
        match matches.opt_str("code-region") {
            Some(s) => vec![range_parse(&s)],
            None => {
                let init_pc: u64 = target.init_pc();
                vec![init_pc..init_pc + 0x10000]
            }
        };
    let init_pc = symbolic_code_regions[0].start;

    // NB: The current aarch64 model needs this, however we explicitly
    // override the PC when setting up the registers.
    lets.insert(ELF_ENTRY, UVal::Init(Val::I128(init_pc as i128)));

    let stop_conditions = StopConditions::parse(matches.opt_strs("kill-at"), &shared_state, StopAction::Kill);
    let exception_stop_conditions = StopConditions::parse(T::exception_stop_functions(), &shared_state, StopAction::Kill);
    let exceptions_allowed_at: HashSet<usize> = matches.opt_strs("exceptions-at").iter().map(|s| s.parse().unwrap_or_else(|e| panic!("Bad instruction index {}: {}", s, e))).collect();

    let little_endian = match matches.opt_str("endianness").as_deref() {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let dump_events = matches.opt_present("events");
    let dump_all_events = matches.opt_present("all-events");
    let mut memory = Memory::new();
    for r in &symbolic_regions {
        memory.add_symbolic_region(r.clone());
    }
    for r in &symbolic_code_regions {
        memory.add_symbolic_code_region(r.clone());
    }

    let instructions = parse_instruction_masks(little_endian, &matches.free);

    let (frame, checkpoint) = init_model(&shared_state, lets, regs, &memory, &target.init_function());
    let (frame, checkpoint, register_map) =
        setup_init_regs(&shared_state, frame, checkpoint, &register_types, init_pc, &target);

    let base_name = &matches.opt_str("output").unwrap_or(String::from("test"));
    let register_bias = !&matches.opt_present("uniform-registers");

    let testconf = TestConf {
        instructions: &instructions,
        max_retries,
        shared_state: &shared_state,
        initial_frame: frame.clone(),
        num_threads,
        dump_events,
        dump_all_events,
        little_endian,
        isa_config: &isa_config,
        encodings: &encodings,
        stop_conditions: &stop_conditions,
        exception_stop_conditions: &exception_stop_conditions,
        exceptions_allowed_at: &exceptions_allowed_at,
        register_types: &register_types,
        symbolic_regions: &symbolic_regions,
        symbolic_code_regions: &symbolic_code_regions,
        assertion_reports: matches.opt_str("assertion-reports"),
        generate_testfile: matches.opt_present("test-file"),
        sparse: matches.opt_present("sparse"),
        init_pc,
        register_map,
    };

    let all_paths_for = matches.opt_get("all-paths-for").expect("Bad all-paths-for argument");

    if number_gens > 1 {
        let mut total_attempts = 0;
        for i in 0..number_gens {
            let mut attempts = 0;
            loop {
                attempts += 1;
                println!("---------- Generating test {} attempt {}", i + 1, attempts);
                let result = match all_paths_for {
                    None => generate_test(
                        &target,
                        &testconf,
                        frame.clone(),
                        checkpoint.clone(),
                        &format!("{}{:03}", base_name, i + 1),
                        register_bias,
                    ),
                    Some(core_instruction) => generate_group_of_tests_around(
                        &target,
                        &testconf,
                        frame.clone(),
                        checkpoint.clone(),
                        &format!("{}{:03}", base_name, i + 1),
                        register_bias,
                        core_instruction,
                    ),
                };
                match result {
                    Ok(()) => break,
                    Err(err) => {
                        println!("Generating test {} attempt {} failed: {}", i + 1, attempts, err);
                        if attempts == 10 {
                            println!("Too many attempts, giving up...");
                            return 1;
                        }
                    }
                }
            }
            total_attempts += attempts;
        }
        println!("---------- Complete, {} tests generated after {} attempts", number_gens, total_attempts);
    } else if number_gens == 1 {
        match all_paths_for {
            None => generate_test(&target, &testconf, frame, checkpoint, base_name, register_bias)
                .unwrap_or_else(|err| println!("Generation attempt failed: {}", err)),
            Some(i) => generate_group_of_tests_around(&target, &testconf, frame, checkpoint, base_name, register_bias, i)
                .unwrap_or_else(|err| println!("Generation attempt failed: {}", err)),
        }
    }

    0
}

struct TestConf<'ir, B: BV> {
    instructions: &'ir [(&'ir str, Option<u32>)],
    max_retries: i32,
    shared_state: &'ir SharedState<'ir, B>,
    initial_frame: Frame<'ir, B>,
    num_threads: usize,
    dump_events: bool,
    dump_all_events: bool,
    little_endian: bool,
    isa_config: &'ir ISAConfig<B>,
    encodings: &'ir Encodings<'ir, B>,
    stop_conditions: &'ir StopConditions,
    exception_stop_conditions: &'ir StopConditions,
    exceptions_allowed_at: &'ir HashSet<usize>,
    register_types: &'ir HashMap<Name, Ty<Name>>,
    symbolic_regions: &'ir [Range<Address>],
    symbolic_code_regions: &'ir [Range<Address>],
    assertion_reports: Option<String>,
    generate_testfile: bool,
    sparse: bool,
    init_pc: u64,
    register_map: HashMap<(String, Vec<extract_state::GVAccessor<String>>), Sym>,
}

#[derive(Debug)]
struct GenerationError(String);

impl std::fmt::Display for GenerationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl Error for GenerationError {}

fn generate_test<'ir, B: BV, T: Target>(
    target: &'ir T,
    conf: &TestConf<'ir, B>,
    mut frame: Frame<'ir, B>,
    mut checkpoint: Checkpoint<B>,
    basename: &str,
    register_bias: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let run_instruction_function = T::run_instruction_function();

    let all_stop_conditions = conf.stop_conditions.union(conf.exception_stop_conditions);

    let mut opcode_vars = vec![];

    let mut opcode_index = 0;
    let mut rng = rand::thread_rng();
    let mut instr_map: HashMap<B, String> = HashMap::new();
    let mut pc_vals: Vec<(Val<B>, String)> = vec![];
    for (i, (instruction, opcode_mask)) in conf.instructions.iter().enumerate() {
        let mut random_attempts_left = conf.max_retries;
        let stop_conds = if conf.exceptions_allowed_at.contains(&i) { conf.stop_conditions } else { &all_stop_conditions };
        loop {
            let (opcode, repeat, description) = instruction_opcode(conf.little_endian, conf.encodings, conf.isa_config, instruction, register_bias);
            instr_map.insert(opcode, description.clone());
            let mask_str = match opcode_mask {
                None => "none".to_string(),
                Some(m) => format!("{:#010x}", m),
            };
            println!("opcode: {}  mask: {}", opcode, mask_str);
            let (opcode_pc, opcode_var, op_checkpoint, opcode_ok) =
                setup_opcode(target, conf.shared_state, &frame, opcode, *opcode_mask, checkpoint.clone());
            let mut continuations =
                if opcode_ok {
                    run_model_instruction(
                        target,
                        &run_instruction_function,
                        conf.num_threads,
                        conf.shared_state,
                        &frame,
                        op_checkpoint,
                        opcode_var,
                        stop_conds,
                        conf.dump_all_events,
                        &conf.assertion_reports,
                    )
                } else {
                    vec![]
                };
            let num_continuations = continuations.len();
            if num_continuations > 0 {
                let (f, c) = continuations.remove(rng.gen_range(0, num_continuations));
                println!("{} successful execution(s)", num_continuations);
                opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                pc_vals.push((opcode_pc, description));
                opcode_index += 1;
                frame = f;
                checkpoint = c;
                break;
            } else {
                println!("No successful executions");
                if repeat {
                    random_attempts_left -= 1;
                    if random_attempts_left == 0 {
                        return Err(Box::new(GenerationError("Retried too many times".to_string())));
                    }
                } else {
                    return Err(Box::new(GenerationError("Unable to continue".to_string())));
                }
            }
        }
    }

    let (entry_reg, exit_reg, c) = finalize(target, conf.shared_state, &frame, checkpoint);
    checkpoint = c;

    println!("Complete");

    if conf.dump_events {
        let trace = checkpoint.trace().as_ref().ok_or(GenerationError("No trace".to_string()))?;
        let mut events = trace.to_vec();
        let events: Vec<Event<B>> = events.drain(..).cloned().rev().collect();
        write_events(&mut std::io::stdout(), &events, &conf.shared_state);
    }

    println!("Initial state extracted from events:");
    let initial_state = extract_state::interrogate_model(
        target,
        conf.isa_config,
        checkpoint,
        conf.shared_state,
        &conf.initial_frame,
        &frame,
        conf.register_types,
        conf.symbolic_regions,
        conf.symbolic_code_regions,
        conf.sparse,
        &conf.register_map,
        &pc_vals,
    )?;
    if conf.generate_testfile {
        generate_testfile::make_testfile(target, basename, &instr_map, initial_state, conf.init_pc, opcode_index)?;
    } else {
        target.make_asm_files(basename, &instr_map, initial_state, entry_reg, exit_reg)?;
        target.build_elf_file(conf.isa_config, basename)?;
    }

    Ok(())
}

fn generate_group_of_tests_around<'ir, B: BV, T: Target>(
    target: &'ir T,
    conf: &TestConf<'ir, B>,
    mut frame: Frame<'ir, B>,
    mut checkpoint: Checkpoint<B>,
    basename: &str,
    register_bias: bool,
    core_instruction_index: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let run_instruction_function = T::run_instruction_function();

    let all_stop_conditions = conf.stop_conditions.union(conf.exception_stop_conditions);

    let mut opcode_vars = vec![];

    let mut opcode_index = 0;
    let mut rng = rand::thread_rng();
    let mut instr_map: HashMap<B, String> = HashMap::new();
    let mut pc_vals: Vec<(Val<B>, String)> = vec![];

    let mut prefix: Vec<(String, Option<u32>)> = conf.instructions.iter().map(|(s,m)| (s.to_string(), *m)).collect();
    let suffix = prefix.split_off(core_instruction_index + 1);
    let (core_instruction, core_opcode_mask) = prefix.pop().expect("Bad index for core instruction");

    // Produce a single continuation for the prefix...
    for (i, (instruction, opcode_mask)) in prefix.iter().enumerate() {
        let mut random_attempts_left = conf.max_retries;
        let stop_conds = if conf.exceptions_allowed_at.contains(&i) { conf.stop_conditions } else { &all_stop_conditions };
        loop {
            let (opcode, repeat, description) = instruction_opcode(conf.little_endian, conf.encodings, conf.isa_config, instruction, register_bias);
            instr_map.insert(opcode, description.clone());
            let mask_str = match opcode_mask {
                None => "none".to_string(),
                Some(m) => format!("{:#010x}", m),
            };
            println!("opcode: {}  mask: {}", opcode, mask_str);
            let (opcode_pc, opcode_var, op_checkpoint, opcode_ok) =
                setup_opcode(target, conf.shared_state, &frame, opcode, *opcode_mask, checkpoint.clone());
            let mut continuations =
                if opcode_ok {
                    run_model_instruction(
                        target,
                        &run_instruction_function,
                        conf.num_threads,
                        conf.shared_state,
                        &frame,
                        op_checkpoint,
                        opcode_var,
                        stop_conds,
                        conf.dump_all_events,
                        &conf.assertion_reports,
                    )
                } else {
                    vec![]
                };
            let num_continuations = continuations.len();
            if num_continuations > 0 {
                let (f, c) = continuations.remove(rng.gen_range(0, num_continuations));
                println!("{} successful execution(s)", num_continuations);
                opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                pc_vals.push((opcode_pc, description));
                opcode_index += 1;
                frame = f;
                checkpoint = c;
                break;
            } else {
                println!("No successful executions");
                if repeat {
                    random_attempts_left -= 1;
                    if random_attempts_left == 0 {
                        return Err(Box::new(GenerationError("Retried too many times".to_string())));
                    }
                } else {
                    return Err(Box::new(GenerationError("Unable to continue".to_string())));
                }
            }
        }
    }

    // ...then take all feasible paths through the core instruction...
    let core_continuations = {
        let i = core_instruction_index;
        let mut random_attempts_left = conf.max_retries;
        let stop_conds = if conf.exceptions_allowed_at.contains(&i) { conf.stop_conditions } else { &all_stop_conditions };
        loop {
            let (opcode, repeat, description) = instruction_opcode(conf.little_endian, conf.encodings, conf.isa_config, &core_instruction, register_bias);
            instr_map.insert(opcode, description.clone());
            let mask_str = match core_opcode_mask {
                None => "none".to_string(),
                Some(m) => format!("{:#010x}", m),
            };
            println!("opcode: {}  mask: {}", opcode, mask_str);
            let (opcode_pc, opcode_var, op_checkpoint, opcode_ok) =
                setup_opcode(target, conf.shared_state, &frame, opcode, core_opcode_mask, checkpoint.clone());
            let continuations =
                if opcode_ok {
                    run_model_instruction(
                        target,
                        &run_instruction_function,
                        conf.num_threads,
                        conf.shared_state,
                        &frame,
                        op_checkpoint,
                        opcode_var,
                        stop_conds,
                        conf.dump_all_events,
                        &conf.assertion_reports,
                    )
                } else {
                    vec![]
                };
            let num_continuations = continuations.len();
            if num_continuations > 0 {
                println!("{} successful execution(s)", num_continuations);
                opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                pc_vals.push((opcode_pc, description));
                opcode_index += 1;
                break continuations;
            } else {
                println!("No successful executions");
                if repeat {
                    random_attempts_left -= 1;
                    if random_attempts_left == 0 {
                        return Err(Box::new(GenerationError("Retried too many times".to_string())));
                    }
                } else {
                    return Err(Box::new(GenerationError("Unable to continue".to_string())));
                }
            }
        }
    };

    // ...and for each run the suffix.
    // We retry if the instructions we chose resulted in no feasible executions
    let mut random_attempts_left = conf.max_retries;
    loop {
        let mut worth_repeating = false;
        let mut had_success = false;
        let mut current_suffix = suffix.clone();

        'cont: for (group_i, (frame, checkpoint)) in core_continuations.iter().enumerate() {
            let mut frame = frame.clone();
            let mut checkpoint = checkpoint.clone();
            println!("Core instruction behaviour {}", group_i + 1);
            for (i, (instruction, opcode_mask)) in current_suffix.iter_mut().enumerate() {
                let stop_conds = if conf.exceptions_allowed_at.contains(&(i + core_instruction_index + 1)) { conf.stop_conditions } else { &all_stop_conditions };
                let (opcode, repeat, description) = instruction_opcode(conf.little_endian, conf.encodings, conf.isa_config, instruction, register_bias);
                *instruction = format!("{:#x} {}", opcode.lower_u64(), description);
                worth_repeating = worth_repeating || repeat;
                instr_map.insert(opcode, description.clone());
                let mask_str = match opcode_mask {
                    None => "none".to_string(),
                    Some(m) => format!("{:#010x}", m),
                };
                println!("opcode: {}  mask: {}", opcode, mask_str);
                let (opcode_pc, opcode_var, op_checkpoint, opcode_ok) =
                    setup_opcode(target, conf.shared_state, &frame, opcode, *opcode_mask, checkpoint.clone());
                let mut continuations =
                    if opcode_ok {
                        run_model_instruction(
                            target,
                            &run_instruction_function,
                            conf.num_threads,
                            conf.shared_state,
                            &frame,
                            op_checkpoint,
                            opcode_var,
                            stop_conds,
                            conf.dump_all_events,
                            &conf.assertion_reports,
                        )
                    } else {
                        vec![]
                    };
                let num_continuations = continuations.len();
                if num_continuations > 0 {
                    let (f, c) = continuations.remove(rng.gen_range(0, num_continuations));
                    println!("{} successful execution(s)", num_continuations);
                    opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                    pc_vals.push((opcode_pc, description));
                    opcode_index += 1;
                    frame = f;
                    checkpoint = c;
                } else {
                    println!("(skipping core instruction behaviour {})", group_i + 1);
                    continue 'cont;
                }
            }

            let (entry_reg, exit_reg, c) = finalize(target, conf.shared_state, &frame, checkpoint);
            checkpoint = c;

            println!("Complete");

            if conf.dump_events {
                let trace = checkpoint.trace().as_ref().ok_or(GenerationError("No trace".to_string()))?;
                let mut events = trace.to_vec();
                let events: Vec<Event<B>> = events.drain(..).cloned().rev().collect();
                write_events(&mut std::io::stdout(), &events, &conf.shared_state);
            }
            
            println!("Initial state extracted from events:");
            match extract_state::interrogate_model(
                target,
                conf.isa_config,
                checkpoint,
                conf.shared_state,
                &conf.initial_frame,
                &frame,
                conf.register_types,
                conf.symbolic_regions,
                conf.symbolic_code_regions,
                conf.sparse,
                &conf.register_map,
                &pc_vals,
            ) {
                Ok(initial_state) => {
                    had_success = true;
                    let basename_number = format!("{}-{:03}", basename, group_i + 1);
                    if conf.generate_testfile {
                        generate_testfile::make_testfile(target, &basename_number, &instr_map, initial_state, conf.init_pc, opcode_index)
                            .unwrap_or_else(
                                |error| println!("Failed to write test file: {}", error.to_string()));
                    } else {
                        target.make_asm_files(&basename_number, &instr_map, initial_state, entry_reg, exit_reg)
                            .map_err(|e| e.to_string())
                            .and_then(
                                |_| target.build_elf_file(conf.isa_config, &basename_number)
                                    .map_err(|e| e.to_string()))
                            .unwrap_or_else(
                                |error| println!("Failed to construct test: {}", error));
                    }
                }
                Err(error) => println!("Failed to extract state: {}", error),
            }
        }

        if had_success { break; };
        println!("Instruction sequence suffix produced no tests");
        if !worth_repeating {
            return Err(Box::new(GenerationError("Unable to continue".to_string())));
        }

        random_attempts_left -= 1;
        if random_attempts_left == 0 {
            return Err(Box::new(GenerationError("Retried too many times".to_string())));
        }
        println!("Trying new suffix");
    }

    Ok(())
}
