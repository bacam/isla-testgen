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

use std::collections::{BTreeMap, HashMap, HashSet};
use std::iter;
use std::fmt;
use std::ops::Range;

use crate::target::Target;
use crate::execution::{apply_accessor_type, apply_accessor_val};
use crate::undef_checker::check_undefined_bits;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::executor::Frame;
use isla_lib::ir;
use isla_lib::ir::{Name, Ty, Val};
use isla_lib::source_loc::SourceLoc;
use isla_lib::log;
use isla_lib::memory;
use isla_lib::smt;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Sym, Checkpoint, Event, Model, SmtResult, Solver};
use isla_lib::zencode;

// TODO: get smt.rs to return a BV
fn bits_to_bv<B: BV>(bits: &[bool]) -> B {
    let mut bv = B::zeros(bits.len() as u32);
    for n in 0..bits.len() {
        if bits[n] {
            bv = bv.set_slice(n as u32, B::BIT_ONE);
        };
    }
    bv
}

// For now I128 values are repesented as bitvectors, because that's
// how they come out of Z3 and we don't really need to convert them to
// anything yet.
#[derive(Clone, Copy, Debug)]
pub enum GroundVal<B> {
    Bool(bool),
    Bits(B, B),  // Value, undef bits
}

impl<B: BV> std::fmt::Display for GroundVal<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundVal::Bool(true) => write!(f, "true"),
            GroundVal::Bool(false) => write!(f, "false"),
            GroundVal::Bits(bs, undefs) => {
                if undefs.is_zero() {
                    std::fmt::Display::fmt(&bs, f)
                } else {
                    write!(f, "{} & {}", bs, !*undefs)
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, Hash)]
pub enum GVAccessor<N> {
    Field(N),
    Element(usize),
}

impl<S, T : PartialEq<S>> PartialEq<GVAccessor<S>> for GVAccessor<T> {
    fn eq(&self, other: &GVAccessor<S>) -> bool {
        use GVAccessor::*;
        match (self, other) {
            (Field(x), Field(y)) => x == y,
            (Element(i), Element(j)) => i == j,
            _ => false
        }
    }
}

fn get_model_val<B: BV>(model: &mut Model<B>, val: &Val<B>, undef: &HashMap<Sym, B>) -> Result<Option<GroundVal<B>>, ExecError> {
    match val {
        Val::Symbolic(var) => match model.get_var(*var)? {
            Some(Exp::Bits64(bits)) => {
                let bits = B::new(bits.lower_u64(), bits.len());
                let undefs = undef.get(var).map(|b| b.clone()).unwrap_or(B::zeros(bits.len()));
                if (!undefs).is_zero() {
                    // Register is undefined, so skip it
                    Ok(None)
                } else {
                    Ok(Some(GroundVal::Bits(bits, undefs)))
                }
            }
            Some(Exp::Bits(bits)) => {
                if bits.len() > 129 {
                    // TODO: a less hacky way of coping with this...
                    // If a read was more than 129 bits then it was a dummy read by the ASL
                    // exclusives modelling to enforce address range constraints and we don't
                    // need to actually handle it
                    Ok(None)
                } else {
                    let bits: B = bits_to_bv(&bits);
                    let undefs = undef.get(var).map(|b| b.clone()).unwrap_or(B::zeros(bits.len()));
                    if (!undefs).is_zero() {
                        // Register is undefined, so skip it
                        Ok(None)
                    } else {
                        Ok(Some(GroundVal::Bits(bits, undefs)))
                    }
                }
            }
            Some(Exp::Bool(b)) => Ok(Some(GroundVal::Bool(b))),
            None => Ok(None),
            Some(exp) => Err(ExecError::Z3Error(format!("Bad bitvector model value {:?}", exp))),
        },
        Val::Bool(b) => Ok(Some(GroundVal::Bool(*b))),
        Val::Bits(bs) => Ok(Some(GroundVal::Bits(*bs, B::zeros(bs.len())))),
        // See comment about I128 above, and note that if we wanted full I128 support we'd need to
        // add a case for symbolic values, above
        Val::I128(i) => Ok(Some(GroundVal::Bits(B::zeros(128).add_i128(*i), B::zeros(128)))),
        _ => Err(ExecError::Type(format!("Bad value {:?} in get_model_val", val), SourceLoc::unknown())),
    }
}

pub struct PrePostStates<'ir, B> {
    pub code: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub pre_memory: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub pre_tag_memory: Vec<(Range<memory::Address>, Vec<bool>)>,
    pub pre_registers: HashMap<(&'ir str, Vec<GVAccessor<&'ir str>>), GroundVal<B>>,
    pub post_memory: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub post_tag_memory: Vec<(memory::Address, bool)>,
    pub post_registers: HashMap<(&'ir str, Vec<GVAccessor<&'ir str>>), GroundVal<B>>,
    pub instruction_locations: HashMap<memory::Address, String>,
}

fn regacc_to_str<B: BV>(shared_state: &ir::SharedState<B>, regacc: &(Name, Vec<GVAccessor<Name>>)) -> String {
    let (reg, acc) = regacc;
    let reg_str = shared_state.symtab.to_str(*reg).to_string();
    let fields = acc.iter().map(|acc| match acc {
        GVAccessor::Field(a) => zencode::decode(shared_state.symtab.to_str(*a)),
        GVAccessor::Element(i) => i.to_string(),
    });
    let parts: Vec<String> = iter::once(reg_str).chain(fields).collect();
    parts.join(".")
}

fn regacc_str_to_str(regacc: &(String, Vec<GVAccessor<String>>)) -> String {
    let (reg, acc) = regacc;
    let fields = acc.iter().map(|acc| match acc {
        GVAccessor::Field(a) => zencode::decode(a),
        GVAccessor::Element(i) => i.to_string(),
    });
    let parts: Vec<String> = iter::once(reg.clone()).chain(fields).collect();
    parts.join(".")
}

impl fmt::Display for GVAccessor<&str> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GVAccessor::Field(s) => write!(f, "{}", s),
            GVAccessor::Element(i) => write!(f, "{}", i),
        }
    }
}

impl fmt::Display for GVAccessor<String> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GVAccessor::Field(s) => write!(f, "{}", s),
            GVAccessor::Element(i) => write!(f, "{}", i),
        }
    }
}

fn regacc_name<'ir, B>(
    shared_state: &ir::SharedState<'ir, B>,
    name: Name,
    accessor: &Vec<GVAccessor<Name>>,
) -> (&'ir str, Vec<GVAccessor<&'ir str>>) {
    (
        shared_state.symtab.to_str(name),
        accessor
            .iter()
            .map(|acc| match acc {
                GVAccessor::Field(field_name) => GVAccessor::Field(shared_state.symtab.to_str(*field_name)),
                GVAccessor::Element(i) => GVAccessor::Element(*i),
            })
            .collect(),
    )
}

fn regacc_int<B>(
    shared_state: &ir::SharedState<B>,
    (name, accessor): &(String, Vec<GVAccessor<String>>),
) -> (Name, Vec<GVAccessor<Name>>) {
    (
        shared_state.symtab.get(&zencode::encode(name)).expect("Register missing"),
        accessor
            .iter()
            .map(|acc| match acc {
                GVAccessor::Field(field_name) => {
                    GVAccessor::Field(shared_state.symtab.get(&zencode::encode(field_name)).expect("Field missing"))
                }
                GVAccessor::Element(i) => GVAccessor::Element(*i),
            })
            .collect(),
    )
}

fn batch_memory<T, F, Element>(
    memory: &BTreeMap<u64, T>,
    content: &F,
    element_range: u64,
) -> Vec<(Range<memory::Address>, Vec<Element>)>
where
    F: Fn(&T) -> Option<Element>,
{
    let mut m = Vec::new();

    let mut current = None;

    for (&address, raw) in memory {
        match content(raw) {
            None => (),
            Some(element) => match current {
                None => current = Some((address..address + element_range, vec![element])),
                Some((old_range, mut elements)) => {
                    if old_range.end == address {
                        elements.push(element);
                        current = Some((old_range.start..address + element_range, elements))
                    } else {
                        m.push((old_range, elements));
                        current = Some((address..address + element_range, vec![element]))
                    }
                }
            },
        }
    }
    match current {
        None => (),
        Some(c) => m.push(c),
    }
    m
}

fn extract_mentioned_registers<B:BV>(events: &[Event<B>]) -> HashSet<Name> {
    let mut mentioned_registers: HashSet<Name> = HashSet::new();
    let mut post_init = false;
    for event in events {
        match event {
            Event::ReadMem { .. } if event.is_ifetch() => post_init = true,
            Event::ReadReg(reg, _, _) | Event::WriteReg(reg, _, _) => {
                if post_init {
                    mentioned_registers.insert(*reg);
                }
            }
            _ => (),
        }
    }
    mentioned_registers
}

/// Extract pre- and post-states from the event trace and the model.
/// The first read after initialisation is recorded for the pre-state:
/// if it was concrete during the symbolic execution then it was
/// initialised separately and the harness doesn't need to do it;
/// however if it's not supported by the harness then we warn about
/// it.
pub fn interrogate_model<'ir, B: BV, T: Target>(
    target: &T,
    _isa_config: &ISAConfig<B>,
    checkpoint: Checkpoint<B>,
    shared_state: &ir::SharedState<'ir, B>,
    _initial_frame: &Frame<'ir, B>,
    final_frame: &Frame<'ir, B>,
    register_types: &HashMap<Name, Ty<Name>>,
    symbolic_regions: &[Range<memory::Address>],
    symbolic_code_regions: &[Range<memory::Address>],
    sparse: bool,
    initial_register_map: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    instruction_pc_vals: &[(Val<B>, String)],
) -> Result<PrePostStates<'ir, B>, ExecError> {
    let mut cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);

    // Ensure that we have symbolic values for all of the post-state registers
    // before we ask for the model, because the target may need to execute
    // encoding (e.g., for capabilities represented as structs)
    let mut final_local_frame = isla_lib::executor::unfreeze_frame(final_frame);
    let mut final_register_vals: HashMap<(String, Vec<GVAccessor<String>>), Val<B>> = HashMap::new();
    for (reg, acc) in target.regs() {
        let name = shared_state.symtab.get(&zencode::encode(&reg)).unwrap();
        let ty = apply_accessor_type(shared_state, register_types.get(&name).unwrap(), &acc);
        if let Some(val) = target.special_reg_encode(
            &reg,
            &acc,
            &ty,
            shared_state,
            &mut final_local_frame,
            &ctx,
            &mut solver
        ) {
            final_register_vals.insert((reg,acc), val);
        } else {
            let full_val = final_local_frame.regs().get_last_if_initialized(name).unwrap();
            let val = apply_accessor_val(shared_state, full_val, &acc);
            final_register_vals.insert((reg,acc), val.clone());
        }
    }

    match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(ExecError::Z3Error(String::from("Unsatisfiable at recheck"))),
        SmtResult::Unknown => return Err(ExecError::Z3Unknown),
    };

    let mut model = Model::new(&solver);
    // Without completing the model we don't always get concrete
    // values for derived values.
    model.set_complete_model(true);
    log!(log::VERBOSE, format!("Model: {:?}", model));

    let mut events = solver.trace().to_vec();
    let events: Vec<Event<B>> = events.drain(..).cloned().rev().collect();
    let undef =
        if target.supports_undef_checker() {
            check_undefined_bits(events.iter(), shared_state.symtab.files()).map_err(|m| ExecError::Unreachable(m))?
        } else {
            HashMap::new()
        };

    let mut instruction_locations = HashMap::new();
    for (pc_val, description) in instruction_pc_vals {
        match get_model_val(&mut model, pc_val, &undef)? {
            Some(GroundVal::Bits(bs, undefs)) => {
                if !undefs.is_zero() {
                    panic!("Location {:?} for instruction {} has undefined bits!", pc_val, description);
                }
                instruction_locations.insert(bs.lower_u64(), description.clone());
            },
            Some(GroundVal::Bool(_)) => panic!("Instruction {} is located at a bool? ({:?})", description, pc_val),
            None => eprintln!("Instruction {} at {:?} doesn't have a concrete location", description, pc_val),
        }
    }

    let harness_registers: HashSet<(Name, Vec<GVAccessor<Name>>)> =
        target.regs().iter().map(|ra| regacc_int(shared_state, ra)).collect();
    let mut initial_memory: BTreeMap<u64, u8> = BTreeMap::new();
    let mut initial_tag_memory: BTreeMap<u64, bool> = BTreeMap::new();
    let mut current_memory: BTreeMap<u64, Option<u8>> = BTreeMap::new();
    let mut current_tag_memory: BTreeMap<u64, Option<bool>> = BTreeMap::new();
    let mut initial_registers: HashMap<(Name, Vec<GVAccessor<Name>>), GroundVal<B>> = HashMap::new();
    let mut current_registers: HashMap<(Name, Vec<GVAccessor<Name>>), Option<GroundVal<B>>> = HashMap::new();

    let mentioned_registers: HashSet<Name> = extract_mentioned_registers(&events);

    // Ensure that system registers that are essential for the harness are included even
    // if they don't appear in the event trace.
    let mut missing: HashSet<(String, Vec<GVAccessor<String>>)> = target.essential_regs().drain(..).collect();

    for regacc in target.regs() {
        if let Some(name) = shared_state.symtab.get(&zencode::encode(&regacc.0)) {
            if missing.contains(&regacc) || mentioned_registers.contains(&name) {
                if let Some(sym) = initial_register_map.get(&regacc) {
                    if let Some(ground_val) = get_model_val(&mut model, &Val::Symbolic(*sym), &undef)? {
                        missing.remove(&regacc);
                        initial_registers.insert(regacc_int(shared_state, &regacc), ground_val);
                    }
                } else {
                    return Err(ExecError::Unreachable(format!("Register {:?} was not initialised", regacc)));
                }
            }
        } else {
            panic!("Missing initial register: {}", regacc.0);
        }
    }
    if !missing.is_empty() {
        let missing: Vec<_> = missing.iter().map(|ra| regacc_str_to_str(ra)).collect();
        return Err(ExecError::Unreachable(format!("Essential system register(s) missing: {}",
                                                  missing.join(", "))));
    }
    for (regacc, val) in final_register_vals {
        if let Some(name) = shared_state.symtab.get(&zencode::encode(&regacc.0)) {
            if mentioned_registers.contains(&name) {
                current_registers.insert(regacc_int(shared_state, &regacc), get_model_val(&mut model, &val, &undef)?);
            }
        } else {
            panic!("Missing final register: {}", regacc.0);
        }
    }

    let mut init_complete = false;

    for event in events {
        match &event {
            // The events in the processor initialisation aren't relevant, so we take
            // them from the first instruction fetch.
            Event::ReadMem { value, read_kind: _, address, bytes, tag_value, opts: _, region: _ } if init_complete || event.is_ifetch() => {
                if !init_complete {
                    init_complete = true;
                }
                let address = match get_model_val(&mut model, address, &undef)? {
                    Some(GroundVal::Bits(bs, undefs)) => {
                        if !undefs.is_zero() {
                            panic!("Memory read address {} has undefined bits {}!", bs, undefs)
                        }
                        bs
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory read address was a boolean?!"),
                    None => panic!("Arbitrary memory read address"),
                };
                let address: u64 = address.try_into()?;
                let val = get_model_val(&mut model, value, &undef)?;
                match val {
                    Some(GroundVal::Bits(val, undefs)) => {
                        if !undefs.is_zero() {
                            panic!("Memory location {} has undefined bits {}", address, undefs);
                        }
                        let vals = val.to_le_bytes();
                        if 8 * *bytes == val.len() {
                            for i in 0..*bytes {
                                let byte_address = address + i as u64;
                                let byte_val = vals[i as usize];
                                if current_memory.insert(byte_address, Some(byte_val)).is_none() {
                                    initial_memory.insert(byte_address, byte_val);
                                }
                            }
                        } else {
                            return Err(ExecError::Type(format!("Memory read had wrong number of bits {} != {}", 8 * *bytes, val.len()), SourceLoc::unknown()));
                        }
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory read returned a boolean?!"),
                    None => println!("Ambivalent read of {} bytes from {:x}", bytes, address),
                }
                match tag_value {
                    Some(tag_value) => {
                        let tag_val = get_model_val(&mut model, tag_value, &undef)?;
                        match tag_val {
                            Some(GroundVal::Bits(v, undefs)) => {
                                if !undefs.is_zero() {
                                    panic!("Tag value at memory location {} is undefined", address);
                                }
                                let tag = !v.is_zero();
                                if current_tag_memory.insert(address, Some(tag)).is_none() {
                                    initial_tag_memory.insert(address, tag);
                                }
                            }
                            Some(GroundVal::Bool(_)) => panic!("Tag memory read returned wrong type (bool)"),
                            None => println!("Ambivalent tag read from {:x}", address),
                        }
                    }
                    None => (),
                }
            }
            Event::WriteMem { value: _, write_kind: _, address, data, bytes, tag_value, opts:_, region: _ } => {
                let address = match get_model_val(&mut model, address, &undef)? {
                    Some(GroundVal::Bits(bs, undefs)) => {
                        if !undefs.is_zero() {
                            panic!("Write to memory location {} has undefined bits", bs);
                        }
                        bs
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory write address was a boolean?!"),
                    None => panic!("Arbitrary memory write address"),
                };
                let address: u64 = address.try_into()?;
                let val = get_model_val(&mut model, data, &undef)?;
                match val {
                    Some(GroundVal::Bits(val, undefs)) => {
                        if !undefs.is_zero() {
                            panic!("Undefined bits {} written to location {}", undefs, address);
                        }
                        let vals = val.to_le_bytes();
                        for i in 0..*bytes {
                            current_memory.insert(address + i as u64, Some(vals[i as usize]));
                        }
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory write value was a boolean?!"),
                    None => {
                        println!("Ambivalent write of {} bytes to {:x}", bytes, address);
                        for i in 0..*bytes {
                            current_memory.insert(address + i as u64, None);
                        }
                    }
                }
                // Even if a tag value is given, some models always include a false value for ordinary
                // writes, so we need to align the address.
                let tag_address = address & ! T::capability_address_mask();
                match tag_value {
                    Some(tag_value) => {
                        let tag_val = get_model_val(&mut model, tag_value, &undef)?;
                        match tag_val {
                            Some(GroundVal::Bits(val, undefs)) => {
                                if !undefs.is_zero() {
                                    panic!("Tag value written to memory location {} is undefined", address);
                                }
                                let tag = !val.is_zero();
                                current_tag_memory.insert(tag_address, Some(tag));
                            }
                            Some(GroundVal::Bool(_)) => panic!("Tag memory write has wrong type (bool)"),
                            None => {
                                println!("Ambivalent tag write to {:x}", address);
                                current_tag_memory.insert(tag_address, None);
                            }
                        }
                    }
                    None => {
                        current_tag_memory.insert(tag_address, Some(false));
                    }
                }
            }
            // Registers are handled directly above, not from the events
            Event::ReadReg(_reg, _accessors, _value) | Event::AssumeReg(_reg, _accessors, _value) => (),
            Event::WriteReg(_reg, _accessors, _value) => (),
            Event::Instr(_) if !init_complete => {
                // We should see the instruction fetch first and look
                // at events from then on
                panic!("Instruction announced without an ifetch");
            }
            _ => (),
        }
    }

    println!("Initial memory:");
    for (address, value) in &initial_memory {
        print!("{:08x}:{:02x} ", address, value);
    }
    println!();
    println!("Initial tag memory:");
    for (address, value) in &initial_tag_memory {
        print!("{:08x}:{}", address, if *value { "t" } else { "f" });
    }
    println!();
    for (regacc, _value) in &initial_registers {
        if !harness_registers.contains(regacc) {
            println!("Warning: depends on unsupported register {}", regacc_to_str(shared_state, regacc));
        }
    }
    print!("Initial registers: ");
    for (regacc, value) in &initial_registers {
        print!("{}:{} ", regacc_to_str(shared_state, regacc), value);
    }
    println!();

    println!("Final memory:");
    for (address, value) in &current_memory {
        match value {
            Some(val) => print!("{:08x}:{:02x} ", address, val),
            None => print!("{:08x}:?? ", address),
        }
    }
    println!();
    println!("Final tag memory:");
    for (address, value) in &current_tag_memory {
        match *value {
            Some(true) => print!("{:08x}:t ", address),
            Some(false) => print!("{:08x}:f ", address),
            None => print!("{:08x}:? ", address),
        }
    }
    println!();
    print!("Final registers: ");
    for (regacc, value) in &current_registers {
        match value {
            Some(val) => print!("{}:{} ", regacc_to_str(shared_state, regacc), val),
            None => print!("{}:?? ", regacc_to_str(shared_state, regacc)),
        }
    }
    println!();

    let (initial_symbolic_memory, initial_symbolic_tag_memory, initial_symbolic_code_memory) =
        if !sparse {
            let mut initial_symbolic_memory: Vec<(Range<memory::Address>, Vec<u8>)> =
                symbolic_regions.iter().map(|r| (r.clone(), vec![0; (r.end - r.start) as usize])).collect();
            
            let mut initial_symbolic_tag_memory: Vec<(Range<memory::Address>, Vec<bool>)> =
                symbolic_regions.iter().map(|r| (r.clone(), vec![false; (r.end - r.start) as usize])).collect();
            
            let mut initial_symbolic_code_memory: Vec<(Range<memory::Address>, Vec<u8>)> =
                symbolic_code_regions.iter().map(|r| (r.clone(), vec![0; (r.end - r.start) as usize])).collect();

            for (address, value) in &initial_memory {
                for (r, v) in &mut initial_symbolic_memory {
                    if r.contains(address) {
                        v[(address - r.start) as usize] = *value;
                        break;
                    }
                }
                for (r, v) in &mut initial_symbolic_code_memory {
                    if r.contains(address) {
                        v[(address - r.start) as usize] = *value;
                        break;
                    }
                }
            }
            for (address, tag) in &initial_tag_memory {
                for (r, v) in &mut initial_symbolic_tag_memory {
                    if r.contains(address) {
                        v[(address - r.start) as usize] = *tag;
                        break;
                    }
                }
            }

            (initial_symbolic_memory, initial_symbolic_tag_memory, initial_symbolic_code_memory)
        } else {
            let (data, code) = initial_memory.iter().partition(|(k,_)| symbolic_regions.iter().any(|r| r.contains(k)));
            (batch_memory(&data, &(|x: &u8| Some(*x)), 1),
             batch_memory(&initial_tag_memory, &(|x: &bool| Some(*x)), 1),
             batch_memory(&code, &(|x: &u8| Some(*x)), 1))
        };

    let pre_registers =
        initial_registers.iter().map(|((reg, acc), gv)| (regacc_name(shared_state, *reg, acc), *gv)).collect();
    let post_registers = current_registers
        .iter()
        .filter_map(|((reg, acc), optional_gv)| match optional_gv {
            Some(gv) => Some((regacc_name(shared_state, *reg, acc), *gv)),
            None => None,
        })
        .collect();
    let post_memory = batch_memory(&current_memory, &(|x: &Option<u8>| *x), 1);

    let mut final_symbolic_tag_memory: Vec<(memory::Address, bool)> = vec![];

    for (address, tag) in &current_tag_memory {
        if let Some(tag) = tag {
            final_symbolic_tag_memory.push((*address, *tag));
        }
    }

    Ok(PrePostStates {
        pre_memory: initial_symbolic_memory,
        pre_tag_memory: initial_symbolic_tag_memory,
        code: initial_symbolic_code_memory,
        pre_registers,
        post_registers,
        post_memory,
        post_tag_memory: final_symbolic_tag_memory,
        instruction_locations,
    })
}
