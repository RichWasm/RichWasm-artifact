use crate::{rwasm::*, translate::QualConst};
use std::collections::HashMap;
use wasabi_wasm as wasm;
use wasm::{FunctionType, ValType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleContext {
    pub(crate) rwasm_global_types: HashMap<u32, PreType>,
    pub(crate) wasm_global_types: HashMap<u32, Vec<ValType>>,
    pub(crate) global_map: HashMap<u32, Vec<u32>>,

    pub(crate) func_types: HashMap<Ind<Function>, crate::rwasm::FunctionType>,
    pub(crate) table: Table,

    pub(crate) malloc: wasm::Instr,
    pub(crate) free: wasm::Instr,
    pub(crate) num_imports: usize,
}

impl ModuleContext {
    pub(crate) fn new(num_imports: usize, table: Table) -> Self {
        ModuleContext {
            rwasm_global_types: HashMap::new(),
            func_types: HashMap::new(),
            wasm_global_types: HashMap::new(),
            global_map: HashMap::new(),

            malloc: wasm::Instr::Call(wasm::Idx::from(0_u32)),
            free: wasm::Instr::Call(wasm::Idx::from(1_u32)),
            num_imports,
            table,
        }
    }

    fn get_wasm_global_list(&self, rwasm_global: u32) -> Vec<u32> {
        self.global_map
            .get(&rwasm_global)
            .unwrap_or_else(|| panic!("Rwasm Global at index {} does not exist.", rwasm_global))
            .to_vec()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FunctionContext {
    pub(crate) typevar_size: HashMap<u32, Size>,
    pub(crate) size_closure: HashMap<u32, u32>,
    pub(crate) qual_closure: HashMap<u32, QualConst>,
    pub(crate) wasm_local_types: HashMap<u32, Vec<ValType>>,
    pub(crate) local_map: HashMap<u32, Vec<u32>>,
}

impl FunctionContext {
    pub(crate) fn new(
        typevar_size: HashMap<u32, Size>,
        size_bounds: &HashMap<u32, (Vec<Size>, Vec<Size>)>,
        qual_bounds: &HashMap<u32, (Vec<Qual>, Vec<Qual>)>,
    ) -> Self {
        FunctionContext {
            typevar_size,
            size_closure: Self::get_size_closure(size_bounds),
            qual_closure: Self::get_qual_closure(qual_bounds),
            wasm_local_types: HashMap::new(),
            local_map: HashMap::new(),
        }
    }

    fn get_wasm_local_list(&self, rwasm_local: u32) -> Vec<u32> {
        self.local_map
            .get(&rwasm_local)
            .unwrap_or_else(|| panic!("Rwasm Local at index {} does not exist.", rwasm_local))
            .to_vec()
    }

    fn i32_to_i64(instrs: &mut Vec<wasm::Instr>) {
        instrs.push(wasm::Instr::Unary(wasm::UnaryOp::I64ExtendI32U))
    }
    fn i64_to_i32(instrs: &mut Vec<wasm::Instr>) {
        instrs.push(wasm::Instr::Unary(wasm::UnaryOp::I32WrapI64))
    }
    fn i64_high(instrs: &mut Vec<wasm::Instr>) {
        // i64 so AND 7FFFFFFF00000000 to get the high 32 bits
        instrs.push(wasm::Instr::Const(wasm::Val::I64(0x7FFFFFFF00000000)));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64And));
    }

    fn i64_low(instrs: &mut Vec<wasm::Instr>) {
        // AND 00000000FFFFFFFF to get the low 32 bits
        instrs.push(wasm::Instr::Const(wasm::Val::I64(0x00000000FFFFFFFF)));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64And));
    }
    fn i64_rotr(instrs: &mut Vec<wasm::Instr>) {
        instrs.push(wasm::Instr::Const(wasm::Val::I64(32)));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Rotr))
    }
    fn i64_rotl(instrs: &mut Vec<wasm::Instr>) {
        instrs.push(wasm::Instr::Const(wasm::Val::I64(32)));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Rotl));
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TempLocal {
    pub(crate) _type: ValType,
    pub(crate) in_use: bool,
}

impl TempLocal {
    fn get_wasm_local(&self) -> wasm::Local {
        wasm::Local {
            type_: self._type,
            name: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TempLocals {
    pub(crate) starting_idx: u32,
    pub(crate) locals: Vec<TempLocal>,
}

impl TempLocals {
    pub(crate) fn new(starting_idx: u32) -> Self {
        TempLocals {
            starting_idx,
            locals: Vec::new(),
        }
    }

    pub(crate) fn get_wasm_locals(&self) -> Vec<wasm::Local> {
        self.locals
            .iter()
            .map(|local| local.get_wasm_local())
            .collect()
    }

    pub(crate) fn get_new_local_var(&mut self, _type: ValType) -> u32 {
        // Find a variable that is not set
        let mut new_local = None;
        for (idx, local) in self.locals.iter_mut().enumerate() {
            if !local.in_use && local._type == _type {
                local.in_use = true;
                new_local = Some((local, self.starting_idx + idx as u32));
            }
        }

        match new_local {
            Some((_, local_idx)) => local_idx,
            None => {
                let new_var_idx = self.starting_idx + self.locals.len() as u32;
                self.locals.push(TempLocal {
                    _type,
                    in_use: true,
                });
                new_var_idx
            }
        }
    }

    pub(crate) fn set_local_var(&mut self, local_idx: u32) -> wasm::Instr {
        // We allow overwrites
        let temp_local_idx = local_idx - self.starting_idx;
        match self.locals.get_mut(temp_local_idx as usize) {
            Some(local) => local.in_use = true,
            None => panic!("Local ind of {local_idx} has not seen before. If this a new variable, use set_new_local_var()"),
        }

        wasm::Instr::Local(wasm::LocalOp::Set, wasm::Idx::from(local_idx))
    }

    pub(crate) fn get_local_var(&self, local_idx: u32) -> wasm::Instr {
        let temp_local_idx = local_idx - self.starting_idx;
        match self.locals.get(temp_local_idx as usize) {
            Some(local) => assert!(local.in_use),
            None => panic!("Local ind of {local_idx} has not seen before. If this a new variable, use set_new_local_var()"),
        }
        wasm::Instr::Local(wasm::LocalOp::Get, wasm::Idx::from(local_idx))
    }

    pub(crate) fn free_local_var(&mut self, local_idx: u32) {
        let temp_local_idx = local_idx - self.starting_idx;
        match self.locals.get_mut(temp_local_idx as usize) {
            Some(local) => local.in_use = false,
            None => panic!("Local ind of {local_idx} has not seen before. If this a new variable, use set_new_local_var()"),
        }
    }
}

pub(crate) fn get_size(ty: ValType) -> i32 {
    match ty {
        ValType::I32 => 32,
        ValType::I64 => 64,
        ValType::F32 => 32,
        ValType::F64 => 64,
    }
}

pub(crate) fn store(ty: ValType) -> wasm::Instr {
    let memarg = wasm::Memarg {
        alignment_exp: 0,
        offset: 0,
    };
    match ty {
        ValType::I32 => wasm::Instr::Store(wasm::StoreOp::I32Store, memarg),
        ValType::I64 => wasm::Instr::Store(wasm::StoreOp::I64Store, memarg),
        ValType::F32 => wasm::Instr::Store(wasm::StoreOp::F32Store, memarg),
        ValType::F64 => wasm::Instr::Store(wasm::StoreOp::F64Store, memarg),
    }
}

pub(crate) fn load(ty: ValType) -> wasm::Instr {
    let memarg = wasm::Memarg {
        alignment_exp: 0,
        offset: 0,
    };
    match ty {
        ValType::I32 => wasm::Instr::Load(wasm::LoadOp::I32Load, memarg),
        ValType::I64 => wasm::Instr::Load(wasm::LoadOp::I64Load, memarg),
        ValType::F32 => wasm::Instr::Load(wasm::LoadOp::F32Load, memarg),
        ValType::F64 => wasm::Instr::Load(wasm::LoadOp::F64Load, memarg),
    }
}

fn resolve_set_operations(
    is_local: bool, //true if the variable is local, false if it's a global variable
    var_shape: &[ValType],
    stack_shape: &[ValType],
    wasm_locals: &[u32],
    temp_locals: &mut TempLocals,
) -> Vec<wasm::Instr> {
    trace!("\nResolving set operations");
    // We have to take the stack shape and put it into the var shape.
    // So we iterate over the stack shape.

    let mut num_locals_set: usize = 0;

    let get_set_instr = |locals_set: &mut usize, wasm_local_idx: u32| -> wasm::Instr {
        *locals_set += 1;
        match is_local {
            true => wasm::Instr::Local(wasm::LocalOp::Set, wasm::Idx::from(wasm_local_idx)),
            false => wasm::Instr::Global(wasm::GlobalOp::Set, wasm::Idx::from(wasm_local_idx)),
        }
    };

    let mut instrs = Vec::new();

    // What does it mean for something to be leftover?
    // There is a value on the stack that is left to be put into a local variable.
    let mut leftover: Option<ValType> = None;

    trace!("  var_shape: {var_shape:?}");
    trace!("stack_shape: {stack_shape:?}");

    for stack_ty in stack_shape.iter() {
        let local_ty = var_shape.get(num_locals_set).unwrap();
        let wasm_local_idx = *wasm_locals.get(num_locals_set).unwrap();

        trace!(
            "leftover:{} stack_ty:{stack_ty:?} var_ty:{local_ty:?}",
            leftover.is_some() as usize
        );

        match (leftover, stack_ty, local_ty) {
            // TOS->[leftover(if any), val ty] -> var ty
            (None, ValType::I32, ValType::I32) | (None, ValType::I64, ValType::I64) => {
                trace!("INSTRS {instrs:?}");
                // [i32|i64] -> i32|i64
                // Type of value on the stack and variable match.
                // No conversion required, do a set.
                let instr = get_set_instr(&mut num_locals_set, wasm_local_idx);
                trace!(": match! no leftover, do set.");
                trace!("  {instr}");
                instrs.push(instr);
            }

            (Some(ValType::I32), ValType::I32, ValType::I32) => {
                // [i32(leftover), i32] -> i32
                // We do a local.set with the TOS (leftover).
                // We do not set leftover to None since the current I32 is leftover.
                trace!(": match! leftover I32, do set and make val on stack leftover!");
                let instr = get_set_instr(&mut num_locals_set, wasm_local_idx);
                trace!("  {instr}");
                instrs.push(instr)
            }

            (Some(ValType::I32), ValType::I64, ValType::I64) => {
                // [i32(leftover), i64] -> i64
                // Split i64 into high and low.
                // Rotate leftover to the left (to make high)
                // Set local var with leftover + high
                // Leave low 32 bits on the stack.
                trace!(": match! but leftover I32 so split 64 and make low 32 bits leftover!");

                let mut pushed_instrs = Vec::new();

                let temp_32 = temp_locals.get_new_local_var(ValType::I32);
                let temp_64 = temp_locals.get_new_local_var(ValType::I64);

                // Save leftover and i64
                pushed_instrs.push(temp_locals.set_local_var(temp_32));
                pushed_instrs.push(temp_locals.set_local_var(temp_64));
                // Get high bits of i64 and rotate to right
                pushed_instrs.push(temp_locals.get_local_var(temp_64));
                FunctionContext::i64_high(&mut pushed_instrs);
                FunctionContext::i64_rotr(&mut pushed_instrs);
                // Extend leftover to i64, rotate to the left
                pushed_instrs.push(temp_locals.get_local_var(temp_32));
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                FunctionContext::i64_rotl(&mut pushed_instrs);
                // Add both together
                pushed_instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Add));
                // Set variable
                pushed_instrs.push(get_set_instr(&mut num_locals_set, wasm_local_idx));
                // Get low 32 bits of local 64 and leave on stack
                pushed_instrs.push(temp_locals.get_local_var(temp_64));
                FunctionContext::i64_low(&mut pushed_instrs);
                FunctionContext::i64_to_i32(&mut pushed_instrs);

                for i in pushed_instrs.iter() {
                    trace!("  {i}")
                }
                instrs.append(&mut pushed_instrs);

                temp_locals.free_local_var(temp_32);
                temp_locals.free_local_var(temp_64);
            }

            (None, ValType::I64, ValType::I32) => {
                // [i64] -> i32
                // Split i64 into high and low bits.
                // Set local variable with high 32 bits.
                // Leave low 32 bits on the stack.

                trace!(": split! I32 leftover");

                leftover = Some(ValType::I32);
                let mut pushed_instrs = Vec::new();

                let temp = temp_locals.get_new_local_var(ValType::I64);

                // Save i64 in temp local variable.
                pushed_instrs.push(temp_locals.set_local_var(temp));
                // Get high bits of i64 and rotate to right
                pushed_instrs.push(temp_locals.get_local_var(temp));
                FunctionContext::i64_high(&mut pushed_instrs);
                FunctionContext::i64_rotr(&mut pushed_instrs);
                // Convert to i32
                FunctionContext::i64_to_i32(&mut pushed_instrs);
                // Set in local variable
                pushed_instrs.push(get_set_instr(&mut num_locals_set, wasm_local_idx));
                // Get low 32 bits of local 64 and leave on stack
                pushed_instrs.push(temp_locals.get_local_var(temp));
                FunctionContext::i64_low(&mut pushed_instrs);
                FunctionContext::i64_to_i32(&mut pushed_instrs);

                temp_locals.free_local_var(temp);

                for i in pushed_instrs.iter() {
                    trace!("  {i}");
                }
                instrs.append(&mut pushed_instrs);
            }

            (None, ValType::I32, ValType::I64) => {
                // [i32] -> i64
                // Make leftover
                trace!(": make leftover");
                leftover = Some(ValType::I32);
            }

            (Some(ValType::I32), ValType::I32, ValType::I64) => {
                // [i32(leftover), i32] -> [i64]
                // Merge the two i32s on the stack and set in local variable.
                // Leftover should be interpreted as high bits of the i64.

                trace!(": merge! found I32 on stack");
                leftover = None;
                let mut pushed_instrs = Vec::new();

                let temp = temp_locals.get_new_local_var(ValType::I32);

                // Save leftover
                pushed_instrs.push(temp_locals.set_local_var(temp));
                // Convert i32 on stack to i64
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                // Get leftover and convert to i64 and rotate to left
                pushed_instrs.push(temp_locals.get_local_var(temp));
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                FunctionContext::i64_rotl(&mut pushed_instrs);
                // Add and save
                pushed_instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Add));
                pushed_instrs.push(get_set_instr(&mut num_locals_set, wasm_local_idx));

                temp_locals.free_local_var(temp);

                for i in pushed_instrs.iter() {
                    trace!("  {i}");
                }
                instrs.append(&mut pushed_instrs);
            }

            // (Some(ValType::I32), ValType::I64, ValType::I32) would be handled by code at the end of the match
            _ => panic!("Unexpected case: {leftover:?} {stack_ty:?} {local_ty:?}"),
        }

        // If the next variable to be set is an I32 and we have a leftover,
        // Do local.set with leftover.
        // Why do we do this at the end of the match instead of in the match itself?
        // You have to leave I64s as leftover you do this in the match, which means more match cases.
        // If we do this, we maintain the invariant that only I32s are leftover.
        if num_locals_set < var_shape.len() {
            let var = var_shape.get(num_locals_set).unwrap();
            let wasm_local_id = *wasm_locals.get(num_locals_set).unwrap();

            if leftover.is_some() && *var == ValType::I32 {
                leftover = None;
                let instr = get_set_instr(&mut num_locals_set, wasm_local_id);
                trace!("             var_ty:{local_ty}: match with leftover");
                trace!("  {instr}");
                instrs.push(instr);
            }
        }
    }

    if let Some(ty) = leftover {
        trace!("Found a stragler leftover {ty}");
        // There is something leftover that should not be leftover 
        // So there is a local.set that is left to be done 
        let local_ty = var_shape.get(num_locals_set).unwrap();
        let wasm_local_idx = *wasm_locals.get(num_locals_set).unwrap();

        match (ty, local_ty) {
            (ValType::I32, ValType::I32) |
            (ValType::I64, ValType::I64) => {
                instrs.push(get_set_instr(&mut num_locals_set, wasm_local_idx));
            }

            (ValType::I32, ValType::I64) => {
                // We want to put an I32 into an I64 
                // Extend i32 on stack to I64 
                // Do local.set              
                FunctionContext::i32_to_i64(&mut instrs);
                instrs.push(get_set_instr(&mut num_locals_set, wasm_local_idx));
            },
            
            _ => panic!("Unexpected case: {leftover:?} {local_ty:?}"),

        }
    }

    instrs
}

fn resolve_get_operations(
    is_local: bool, //true if the variable is local, false if it's a global variable
    var_shape: &[ValType],
    stack_shape: &[ValType],
    wasm_locals: &[u32],
) -> Vec<wasm::Instr> {
    trace!("\nResolve get operations");
    
    // We have a variable shape and have to put it into the stack shape.
    // So we go over variable shape

    let get_get_instr = |wasm_local_idx: u32| -> wasm::Instr {
        match is_local {
            true => wasm::Instr::Local(wasm::LocalOp::Get, wasm::Idx::from(wasm_local_idx)),
            false => wasm::Instr::Global(wasm::GlobalOp::Get, wasm::Idx::from(wasm_local_idx)),
        }
    };

    let mut instrs: Vec<wasm::Instr> = Vec::new();

    // What does it mean for something to be leftover?
    // It means that there is something on the stack that doesn't exactly fit the stack slot type needed.
    let mut leftover: Option<ValType> = None;

    trace!("  var_shape: {var_shape:?}");
    trace!("stack_shape: {stack_shape:?}");

    // We do gets from the opposite direction that we did the sets.
    // This means that since we did local.sets from 0 to wasm_locals length, we do local.gets from wasm_locals length to 0
    let total_wasm_locals = wasm_locals.len();
    let mut num_slot = 0;
    let mut num_local_get = total_wasm_locals;

    for (i, local_ty) in var_shape.iter().rev().enumerate() {
        num_local_get = total_wasm_locals - 1 - i;
        let stack_ty = stack_shape.get(num_slot).unwrap();
        let wasm_local_idx = *wasm_locals.get(num_local_get).unwrap();

        trace!(
            "leftover:{} stack_ty:{stack_ty:?} var_ty:{local_ty:?}",
            leftover.is_some() as usize
        );

        match (leftover, local_ty, stack_ty) {
            // TOS->[leftover]; local ty -> [stack_ty]
            (None, ValType::I32, ValType::I32) | (None, ValType::I64, ValType::I64) => {
                // []; i32|i64 -> [i32|i64]
                // No conversion required, do a get.
                let instr = get_get_instr(wasm_local_idx);
                trace!(": match! no leftover, local.get.");
                trace!("  {instr}");
                instrs.push(instr);
                num_slot += 1;
            }

            (Some(ValType::I32), ValType::I32, ValType::I32) => {
                // [i32]; i32 -> [i32]
                // The stack already has an i32, leave it there.
                // The value from local.get is leftover.
                let instr = get_get_instr(wasm_local_idx);
                trace!(": match! leftover local.get.");
                trace!("  {instr}");
                instrs.push(instr);
                num_slot += 1;
            }

            (Some(ValType::I32), ValType::I64, ValType::I64) => {
                // [i32]; i64 -> [i64]
                // The stack has an i32 which should be interpreted as the low bits of the i64 to be produced.
                // The low of the i64 in the local should be interpreted as the high bits of the i64 to be produced.
                // We leave the high of the i64 in the local on the stack.

                trace!(": match! but leftover I32 so split 64 and make low 32 bits leftover!");
                let mut pushed_instrs = Vec::new();

                // Extend i32 on the stack to i64 (it is already the low bits)
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                // Local.get
                pushed_instrs.push(get_get_instr(wasm_local_idx));
                // Get low bits of the i64 in the local
                FunctionContext::i64_low(&mut pushed_instrs);
                // Rotate to the left since it the high bits of the slot
                FunctionContext::i64_rotl(&mut pushed_instrs);
                // Add
                pushed_instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Add));
                // Local.get
                pushed_instrs.push(get_get_instr(wasm_local_idx));
                // Get high bits of the i64 in the local
                FunctionContext::i64_high(&mut pushed_instrs);
                // Rotate right
                FunctionContext::i64_rotr(&mut pushed_instrs);
                // Convert to 32 and leave on the stack
                FunctionContext::i64_to_i32(&mut pushed_instrs);

                for i in pushed_instrs.iter() {
                    trace!("  {i}")
                }

                instrs.append(&mut pushed_instrs);
                num_slot += 1;
            }

            (None, ValType::I32, ValType::I64) => {
                // [] ; i32 -> [i64]
                // Do a local.get and leave on the stack
                leftover = Some(ValType::I32);
                let instr = get_get_instr(wasm_local_idx);
                trace!(": make leftover");
                trace!("  {instr}");
                instrs.push(instr);
            }

            (None, ValType::I64, ValType::I32) => {
                // [] ; i64 -> [i32]
                // Get low bits of i64 in local. Interpret as i32 on the stack.
                // Leave the high bits of the i64 in local on the stack.

                trace!(": split! leave i32 on the stack");
                leftover = Some(ValType::I32);
                let mut pushed_instrs = Vec::new();

                // Local.get
                pushed_instrs.push(get_get_instr(wasm_local_idx));
                // Get low bits
                FunctionContext::i64_low(&mut pushed_instrs);
                // Convert to I32
                FunctionContext::i64_to_i32(&mut pushed_instrs);
                // Local.get
                pushed_instrs.push(get_get_instr(wasm_local_idx));
                // Get high bits
                FunctionContext::i64_high(&mut pushed_instrs);
                // Rotate to right
                FunctionContext::i64_rotr(&mut pushed_instrs);
                // Convert to I32 and leave on the stack
                FunctionContext::i64_to_i32(&mut pushed_instrs);

                for i in pushed_instrs.iter() {
                    trace!("  {i}")
                }
                instrs.append(&mut pushed_instrs);
                num_slot += 1;
            }

            (Some(_), ValType::I32, ValType::I64) => {
                // [i32] ; i32 -> i64
                // The stack has an i32 which should be interpreted as the low bits of the i64 to be produced.
                // The i32 in the local in the high bits of the i64 to be produced.

                leftover = None;
                trace!(": merge! i32 is leftover, merge with local i32");
                let mut pushed_instrs = Vec::new();

                // Convert i32 on stack to i64 (it is already in low bits of the i64)
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                // Local.get
                pushed_instrs.push(get_get_instr(wasm_local_idx));
                // Convert i32 in local to i64
                FunctionContext::i32_to_i64(&mut pushed_instrs);
                // Rotate to left to make the high bits
                FunctionContext::i64_rotl(&mut pushed_instrs);
                // Add
                pushed_instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I64Add));

                for i in pushed_instrs.iter() {
                    trace!("  {i}")
                }
                instrs.append(&mut pushed_instrs);
                num_slot += 1;
            }

            // (Some(_), ValType::I64, ValType::I32) => {} Case handled by code after the match statement.
            _ => panic!("Unexpected case: {leftover:?} {stack_ty:?} {local_ty:?}"),
        }

        // If the type expected on the stack is an I32 and we have a leftover,
        // Set leftover to None to leave it on the stack.
        // Why do we do this at the end of the match instead of in the match itself?
        // You have to leave I64s as leftover you do this in the match, which means more match cases.
        // If we do this, we maintain the invariant that only I32s are leftover.
        if num_slot < stack_shape.len() {
            let stack_ty = stack_shape.get(num_slot).unwrap();
            if leftover.is_some() && *stack_ty == ValType::I32 {
                trace!("leftover:1 stack_ty:I32           : match! leave on stack");
                leftover = None;
                num_slot += 1;
            }
        }
    }


    if let Some(ty) = leftover {
        // There is something leftover that should not be leftover 
        // So there *might* be a local.get that is left to be done 
        let stack_ty = stack_shape.get(num_slot);
        match stack_ty {
            // There are no more stack types that are left to produce so please drop  
            None => instrs.push(wasabi_wasm::Instr::Drop),
                        
            // There is a stack type left to produce! How convinent
            Some(stack_ty) => {
                assert!(false); 
                // This will probably never be called but idk 
                let wasm_local_idx = *wasm_locals.get(num_local_get).unwrap();
                match (ty, stack_ty) {
                    (ValType::I32, ValType::I32) |
                    (ValType::I64, ValType::I64) => {
                        instrs.push(get_get_instr(wasm_local_idx));
                    }
            
                    (ValType::I32, ValType::I64) => {
                        // There is an I32 on the stack that should be an I64 
                        FunctionContext::i32_to_i64(&mut instrs);
                        instrs.push(get_get_instr(wasm_local_idx));
                    },
                    
                    _ => panic!("Unexpected case: {leftover:?} {stack_ty:?}"),
            
                }
            }
        
        }        

    }

    instrs
}

pub(crate) fn translate_instr(
    instr: &Instr,
    fun_ctx: &FunctionContext,
    mod_ctx: &ModuleContext,
    temp_locals: &mut TempLocals,
) -> Vec<wasm::Instr> {
    match instr {
        // TOS->[stack state before instruction] -> [stack state after instruction]
        Instr::Block(bt, _, body) | Instr::Loop(bt, body) => {
            trace!("Translating Block/Loop");
            let (params, results) = bt.get_wasm_types(fun_ctx);
            // Erase local effect, compile type
            // We are compiling to Multivalue Wasm where blocks can take in
            // zero or more arguments and produce zero or more results

            let mut result_vec = vec![wasm::Instr::Block(wasm::FunctionType::new(
                &params, &results,
            ))];
            result_vec.append(
                &mut body
                    .iter()
                    .flat_map(|inst| translate_instr(inst, fun_ctx, mod_ctx, temp_locals))
                    .collect(),
            );
            result_vec.push(wasm::Instr::End);
            result_vec
        }

        Instr::IfThenElse(bt, _le, if_body, else_body) => {
            trace!("Translating IfThenElse");
            let (params, results) = bt.get_wasm_types(fun_ctx);

            let mut instrs = vec![wasm::Instr::If(wasm::FunctionType::new(&params, &results))];
            instrs.append(
                &mut if_body
                    .iter()
                    .flat_map(|inst| translate_instr(inst, fun_ctx, mod_ctx, temp_locals))
                    .collect(),
            );
            if !else_body.is_empty() {
                instrs.push(wasm::Instr::Else);
                instrs.append(
                    &mut else_body
                        .iter()
                        .flat_map(|inst| translate_instr(inst, fun_ctx, mod_ctx, temp_locals))
                        .collect(),
                );
            }
            instrs.push(wasm::Instr::End);
            instrs
        }

        Instr::Array(op, _type) => {
            trace!("Translating Array");

            let mut instrs = Vec::new();

            match op {
                // array.malloc : [init val*, number of cells] -> [ptr]
                ArrayOp::Malloc(_qual) => {
                    // Save the number of cells
                    let num_cells = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(num_cells));

                    // Get the wasm_types the array type converts to.
                    let wasm_types = _type.to_wasm_types(fun_ctx);

                    // Go through wasm_types: save init values and calculate the total size of array.
                    let (wasm_locals, size): (Vec<u32>, Vec<i32>) = wasm_types
                        .iter()
                        .map(|wasm_ty| {
                            let local = temp_locals.get_new_local_var(*wasm_ty);
                            instrs.push(temp_locals.set_local_var(local));
                            (local, get_size(*wasm_ty))
                        })
                        .unzip();

                    // Call malloc on total size of array
                    let array_total_size = size.iter().fold(0, |acc, curr| acc + *curr);
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(array_total_size)));
                    instrs.push(mod_ctx.malloc.clone());

                    // Save the pointer returned by malloc
                    let array_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(array_ptr));

                    // Initialize a working pointer to the start of array.
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    let get_struct_ptr = temp_locals.get_local_var(array_ptr);
                    let set_working_ptr = temp_locals.set_local_var(working_ptr);
                    let get_working_ptr = temp_locals.get_local_var(working_ptr);

                    instrs.push(get_struct_ptr.clone());
                    instrs.push(set_working_ptr.clone());

                    // Loop,
                    //  if num_cells > 0:
                    //    for each wasm val type
                    //      Fetch working pointer
                    //      Load init value from respective local variable
                    //      Store in memory
                    //      working ptr = working ptr + size of wasm val type
                    //    num_cells = num_cells - 1;
                    //    br @loop, ie, restart loop
                    instrs.push(wasm::Instr::Loop(wasm::FunctionType::new(&[], &[])));

                    // Check that num_cells is greater than zero
                    // If you have a 0 on the stack, the condition fails, so just push num_cells on the stack
                    instrs.push(temp_locals.get_local_var(num_cells));
                    instrs.push(wasm::Instr::If(wasm::FunctionType::new(&[], &[])));

                    // then body of the if
                    // Store init value(s) and update working pointer
                    for (wasm_ty, wasm_local) in
                        wasm_types.iter().rev().zip(wasm_locals.iter().rev())
                    {
                        instrs.push(get_working_ptr.clone());
                        instrs.push(temp_locals.get_local_var(*wasm_local));
                        instrs.push(store(*wasm_ty));

                        instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
                        instrs.push(get_working_ptr.clone());
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                        instrs.push(set_working_ptr.clone());
                    }

                    // Decrement num cells
                    instrs.push(temp_locals.get_local_var(num_cells));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(1)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                    instrs.push(temp_locals.set_local_var(num_cells));

                    // Restart the loop
                    instrs.push(wasm::Instr::Br(wasm::Label::from(1_u32)));

                    // End the if statement and loop
                    instrs.push(wasm::Instr::End);
                    instrs.push(wasm::Instr::End);

                    // Free up working pointer and locals
                    temp_locals.free_local_var(working_ptr);
                    wasm_locals
                        .iter()
                        .for_each(|local| temp_locals.free_local_var(*local));

                    // Return array pointer
                    instrs.push(get_struct_ptr);
                    temp_locals.free_local_var(array_ptr);

                    trace!("array malloc");
                    instrs.iter().for_each(|i| trace!("  {i}"));
                }

                // array.get : [ptr ind] -> [ptr, val* at ind]
                ArrayOp::Get => {
                    // Save array index
                    let ind = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(ind));

                    // Save the array pointer on TOS
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // Calulate the offset of the field from the start of the array (size of type*(ind))
                    let size_of_type = _type.to_u32(fun_ctx);
                    instrs.push(temp_locals.get_local_var(ind));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(size_of_type as i32)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Mul));

                    temp_locals.free_local_var(ind);

                    // Calculate the working pointer to be struct pointer + offset
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));

                    // Push stack pointer on stack to return
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    temp_locals.free_local_var(struct_ptr);

                    // Calculate the wasm_types the rwasm type corresponds to
                    let wasm_types = _type.to_wasm_types(fun_ctx);

                    // Go through wasm types in order, for each,
                    for wasm_ty in wasm_types {
                        // Do appropriate memory.load
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(load(wasm_ty));

                        //   Update the working pointer with size of the type
                        let wasm_ty_size = wasm::Instr::Const(wasm::Val::I32(get_size(wasm_ty)));
                        instrs.push(wasm_ty_size);
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                        instrs.push(temp_locals.set_local_var(working_ptr));
                    }

                    temp_locals.free_local_var(working_ptr);

                    trace!("array get");
                    instrs.iter().for_each(|i| trace!("  {i}"));
                }

                // array.set : [ptr ind val*] -> ptr
                ArrayOp::Set => {
                    // Calculate the wasm_types the rwasm type corresponds to
                    let wasm_types = _type.to_wasm_types(fun_ctx);

                    // Save data* in locals
                    let mut locals = Vec::new();
                    for wasm_ty in wasm_types.iter().rev() {
                        let local = temp_locals.get_new_local_var(*wasm_ty);
                        instrs.push(temp_locals.set_local_var(local));
                        locals.push(local);
                    }

                    // Save ind
                    let ind = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(ind));

                    // Save the array pointer on TOS
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // Calculate offset as size of type * (ind+1) (we go to the end of the field since we work in reverse)
                    let size_of_type = _type.to_u32(fun_ctx);
                    instrs.push(temp_locals.get_local_var(ind));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(1)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));                    
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(size_of_type as i32)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Mul));

                    temp_locals.free_local_var(ind);

                    // Calculate the working pointer to be struct pointer + offset and save in local variable.
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));

                    // Now, for each wasm_ty, in reverse,
                    for (wasm_ty, data) in wasm_types.iter().rev().zip(locals.iter().rev()) {
                        // Update the working pointer as working pointer - size of type.
                        let wasm_ty_size = wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty)));
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(wasm_ty_size);
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                        instrs.push(temp_locals.set_local_var(working_ptr));

                        // Store [ptr data] -> []
                        // The data is already TOS so load working pointer and store in memory
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(temp_locals.get_local_var(*data));
                        instrs.push(store(*wasm_ty));

                        temp_locals.free_local_var(*data);
                    }
                    temp_locals.free_local_var(working_ptr);

                    // Return saved stack pointer.
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    temp_locals.free_local_var(struct_ptr);

                    trace!("array set");
                    instrs.iter().for_each(|i| trace!("  {i}"));
                }

                // array.free : [ptr] -> []
                ArrayOp::Free => {
                    instrs.push(mod_ctx.free.clone());
                }
            }
            instrs
        }

        Instr::Struct(op, value_types) => {
            trace!("Translating Struct");
            
            let mut instrs: Vec<wasm::Instr> = Vec::new();

            match op {
                // struct.malloc : [t*] -> [ptr]
                StructOp::Malloc(struct_field_sizes, _qual) => {
                    // Get the total size of struct
                    let struct_total_size = struct_field_sizes
                        .iter()
                        .fold(Size::Concrete(0), |total, current| {
                            Size::Plus(Box::new(total), Box::new(current.clone()))
                        })
                        .to_u32(&fun_ctx.size_closure)
                        as i32;
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(struct_total_size)));

                    // Call malloc
                    instrs.push(mod_ctx.malloc.clone());

                    // Save the pointer returned by malloc
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // We have to now initialize each of the fields to the initialization value on the stack.
                    // The initialization values are stored in reverse order, ie,
                    // If you're doing a struct.malloc of sizes, 32, 32, 64
                    // Values are pushed in 32, 32, 64 order before the malloc,
                    // Which means that when you set the default values in the field,
                    // you have to do it in reverse order.

                    // Initialize a working pointer to the end of the stack.
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    let get_struct_ptr = temp_locals.get_local_var(struct_ptr);
                    let set_working_ptr = temp_locals.set_local_var(working_ptr);
                    let get_working_ptr = temp_locals.get_local_var(working_ptr);

                    instrs.push(get_struct_ptr);
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(struct_total_size)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(set_working_ptr.clone());

                    for ty in value_types.iter().rev() {
                        let ty = ty.get_pt();
                        let wasm_types = ty.to_wasm_types(fun_ctx);

                        // The wasm values will be in reverse of what is expected since they are popped from the stack
                        for wasm_ty in wasm_types.iter().rev() {
                            // At the moment, the initialization value is at TOS and needs to be
                            // temporarily saved since it should be on stack after memory.
                            let data = temp_locals.get_new_local_var(*wasm_ty);
                            instrs.push(temp_locals.set_local_var(data));
                            trace!("{wasm_ty} {data}");

                            // Store: [ptr data] -> []

                            // We need to store data at pointer - size of wasm_ty
                            instrs.push(get_working_ptr.clone());
                            instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
                            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                            instrs.push(set_working_ptr.clone());

                            // Load ptr and data and call appropraite memory store instruction
                            instrs.push(get_working_ptr.clone());
                            instrs.push(temp_locals.get_local_var(data));
                            instrs.push(store(*wasm_ty));

                            temp_locals.free_local_var(data);
                        }
                    }

                    temp_locals.free_local_var(working_ptr);

                    // Return struct pointer
                    let ret_struct_ptr = temp_locals.get_local_var(struct_ptr);
                    trace!(" {} // Return struct pointer", ret_struct_ptr);

                    instrs.push(ret_struct_ptr);
                    temp_locals.free_local_var(struct_ptr);
                }

                // struct.get : [ptr] -> [ptr, val* at ind]
                StructOp::Get(ind) => {
                    let ind = *ind as usize;

                    // Save the struct pointer on TOS
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // Get the (rwasm) type of struct field with ind and
                    // calculate the wasm_types this corresponds to.
                    let rwasm_type_of_field = value_types
                        .get(ind)
                        .unwrap_or_else(|| panic!("Struct does not have field number {ind}"));
                    let wasm_types_of_field = rwasm_type_of_field.to_wasm_types(fun_ctx);

                    // Calulate the offset of the field from the start of the struct
                    let offset = value_types[0..ind]
                        .iter()
                        .fold(0, |acc, curr| acc + curr.to_u32(fun_ctx));

                    // Calculate the working pointer to be struct pointer + offset
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(offset as i32)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));

                    // Push stack pointer on stack to return
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    temp_locals.free_local_var(struct_ptr);

                    // Go through wasm types in order, for each,
                    for wasm_ty in wasm_types_of_field {
                        // Do appropriate memory.load
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(load(wasm_ty));

                        // Update the working pointer with size of the type
                        let wasm_ty_size = wasm::Instr::Const(wasm::Val::I32(get_size(wasm_ty)));
                        instrs.push(wasm_ty_size);
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                        instrs.push(temp_locals.set_local_var(working_ptr));
                    }
                    temp_locals.free_local_var(working_ptr);
                }

                // struct.set : [ptr, t*] -> [ptr]
                StructOp::Set(ind, pt ) => {

                    if let PreType::Unit = pt {
                        return vec![]
                    }

                    let ind = *ind as usize;

                    // Get the (rwasm) type of struct field with ind and
                    // calculate the wasm_types this corresponds to.
                    let rwasm_type_of_field = value_types
                        .get(ind)
                        .unwrap_or_else(|| panic!("Struct does not have field number {ind}"));
                    let wasm_types_of_field = rwasm_type_of_field.to_wasm_types(fun_ctx);

                    // Save all the data to be set
                    let mut locals = Vec::new();
                    for wasm_ty in wasm_types_of_field.iter().rev() {
                        let local = temp_locals.get_new_local_var(*wasm_ty);
                        instrs.push(temp_locals.set_local_var(local));
                        locals.push(local);
                    }

                    // Save the struct pointer on TOS
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // Calulate the offset of the field from the start of the struct
                    let offset = value_types[0..ind]
                        .iter()
                        .fold(0, |acc, curr| acc + curr.to_u32(fun_ctx));

                    // Calculate the working pointer to be struct pointer + offset
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(offset as i32)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));

                    // Now, for each wasm_ty, in reverse,
                    for (wasm_ty, data) in wasm_types_of_field.iter().rev().zip(locals.iter().rev())
                    {
                        // Update the working pointer as working pointer - size of type.
                        let wasm_ty_size = wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty)));
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(wasm_ty_size);
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                        instrs.push(temp_locals.set_local_var(working_ptr));

                        // Store [ptr data] -> []
                        // The data is already TOS so load working pointer and store in memory
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(temp_locals.get_local_var(*data));
                        instrs.push(store(*wasm_ty));

                        temp_locals.free_local_var(*data);
                    }
                    temp_locals.free_local_var(working_ptr);

                    // Return saved stack pointer.
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    temp_locals.free_local_var(struct_ptr);

                    trace!("Struct set:");
                    instrs.iter().for_each(|i| trace!("  {i}"));
                }

                // struct.free : [ptr] -> []
                StructOp::Free => {
                    // wfree just needs the pointer and keeps track of how big/small things are,
                    // so there's no need to get the size of the struct (or array) to free it.
                    instrs.push(mod_ctx.free.clone());
                }

                // struct.swap : [ptr, t*] -> [ptr, t_old*]
                StructOp::Swap(ind, pt, ) => {

                    let setting_unit = match pt {
                        PreType::Unit => true,
                        _ => false
                    }; 

                    let ind = *ind as usize;

                    // Get the (rwasm) type of struct field with ind and
                    // calculate the wasm_types this corresponds to.
                    let rwasm_type_of_field = value_types
                        .get(ind)
                        .unwrap_or_else(|| panic!("Struct does not have field number {ind}"));
                    let wasm_types_of_field = rwasm_type_of_field.to_wasm_types(fun_ctx);

                    // Save all the data to be set
                    let mut locals = Vec::new();
                    for wasm_ty in wasm_types_of_field.iter().rev() {
                        let local = temp_locals.get_new_local_var(*wasm_ty);
                        if !setting_unit {
                            instrs.push(temp_locals.set_local_var(local));
                        }
                        locals.push(local);
                    }

                    // Save the struct pointer on TOS
                    let struct_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.set_local_var(struct_ptr));

                    // Calulate the offset of the field from the start of the struct
                    let offset = value_types[0..ind]
                        .iter()
                        .fold(0, |acc, curr| acc + curr.to_u32(fun_ctx));

                    // Calculate the working pointer to be struct pointer + offset
                    let working_ptr = temp_locals.get_new_local_var(ValType::I32);
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(offset as i32)));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));

                    // We have to save old values.
                    let mut old_values = Vec::new();

                    // Now, for each wasm_ty, in reverse,
                    for (wasm_ty, data) in wasm_types_of_field.iter().rev().zip(locals.iter().rev())
                    {
                        // Update the working pointer as working pointer - size of type.
                        // Update the working pointer with size of the type
                        let wasm_ty_size = wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty)));
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(wasm_ty_size);
                        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                        instrs.push(temp_locals.set_local_var(working_ptr));

                        // Load from memory and store in temporary variable.
                        instrs.push(temp_locals.get_local_var(working_ptr));
                        instrs.push(load(*wasm_ty));
                        let old_data = temp_locals.get_new_local_var(*wasm_ty);
                        instrs.push(temp_locals.set_local_var(old_data));
                        old_values.push(old_data);

                        if !setting_unit {
                            // Store [ptr data] -> []
                            // The data is already TOS so load working pointer and store in memory
                            instrs.push(temp_locals.get_local_var(working_ptr));
                            instrs.push(temp_locals.get_local_var(*data));
                            instrs.push(store(*wasm_ty));
                        }

                        temp_locals.free_local_var(*data);
                    }
                    temp_locals.free_local_var(working_ptr);

                    // Return saved stack pointer.
                    instrs.push(temp_locals.get_local_var(struct_ptr));
                    temp_locals.free_local_var(struct_ptr);

                    // Return old values
                    for old_data in old_values {
                        instrs.push(temp_locals.get_local_var(old_data));
                        temp_locals.free_local_var(old_data);
                    }

                    trace!("Struct swap: ");
                    instrs.iter().for_each(|i| trace!("  {i}"));
                }
            }
            instrs
        }

        // call : [p*] -> [r*]
        Instr::Call(ind, vars) => {
            trace!("Translating Call");

            // Why do we need Vec<Index>?
            // The function you are calling might have size variables that have to instantiated.
            // We store all instantiated variables in a pointer and pass it to the function being called.
            // In principle, Type variables are the only things that need to be boxed so we box each type variable.
            // If a function returns a type variable, we need to unbox from the heap so that the stack shape is as expected.

            //                   i32 i64              i32 i64
            // callee type: [i32 typevar i64] -> [i64 typevar i32]
            //
            //        +-----------------------------------------------+
            //        |    wasm     | rwasm |   rwasm    |    wasm    |
            //        | before call |  call | after call | after call |
            //        +-----------------------------------------------+
            //        |     i32     |  i32  |    i64     |    i64     |
            //        |     i32     |  i64  |    i64     |    i32     |
            //        |     i64     |  i64  |    i32     |    i64     |
            //        |     i64     |       |            |    i32     |
            // TOS -> +-----------------------------------------------+

            let mut instrs: Vec<wasm::Instr> = Vec::new();

            let callee_ft = mod_ctx.func_types.get(ind).unwrap_or_else(|| {
                panic!(
                    "Trying to call a function that does not exist: Function {}",
                    ind.0 + mod_ctx.num_imports as u32
                )
            });

            let (_callee_wasm_tys, callee_fun_ctx) = callee_ft.get_wasm_types();

            let mut type_var_types = HashMap::new();
            let mut type_var_count = 0;
            vars.iter().for_each(|var| match var {
                // We do not care about size, loc and qual variables
                Index::Size(_) | Index::Loc(_) | Index::Qual(_) => (),
                Index::PreType(pt) => {
                    type_var_types.insert(type_var_count, pt.clone());
                    type_var_count += 1;
                }
            });

            let caller_params = callee_ft
                .params
                .iter()
                .map(|p| p.instantiate_ty(&type_var_types))
                .collect::<Vec<_>>();

            // Transform the wasm stack to the rwasm calling convention
            match crate::rwasm::FunctionType::to_callee_stack(
                &caller_params,
                &callee_ft.params,
                fun_ctx,
                &callee_fun_ctx,
                mod_ctx,
                &mut instrs,
                temp_locals,
            ) {
                Ok(_) => (),
                Err(_) => panic!("To callee stack transformation failed because they had different concrete types. Caller stack:{caller_params:?}, Callee stack:{:?}", &callee_ft.params),
            }

            // Call the function
            let func_call_ind = ind.0 + mod_ctx.num_imports as u32;
            instrs.push(wasm::Instr::Call(wasm::Idx::from(func_call_ind)));

            let caller_results = callee_ft
                .results
                .iter()
                .map(|p| p.instantiate_ty(&type_var_types))
                .collect::<Vec<_>>();

            // Transform the rwasm calling convention to the wasm stack expected.
            // The function might return type variables in which case,
            // they need to be unboxed in order and put on the stack.
            match crate::rwasm::FunctionType::to_caller_stack(
                &caller_results,
                &callee_ft.results,
                fun_ctx,
                &callee_fun_ctx,
                mod_ctx,
                &mut instrs,
                temp_locals,
            ) {
                Ok(_) => (),
                Err(_) => panic!("To caller stack transformation failed because they had different concrete types. Caller stack:{caller_results:?}, Callee stack:{:?}", &callee_ft.results),
            }

            instrs
        }

        // coderef : [] -> [i32] (ind)
        // coderef instructions compile to an i32 index into the function table
        Instr::CodeRef(ind) => {
            trace!("Translating Coderef");
            vec![wasm::Instr::Const(wasm::Val::I32(ind.0 as i32))]
        },

        // inst : [] -> []
        Instr::Inst(_indicies) => vec![],

        // call_indirect : [p*, ptr] -> [r*]
        Instr::CallIndirect(bt) => {
            trace!("Translating CallIndirect Instruction");
            let mut instrs = Vec::new();

            // Save index on TOS
            let coderef_idx = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.set_local_var(coderef_idx));

            // Collect possible function types from call
            let mut possible_funs = Vec::new();
            mod_ctx
                .table
                .entries
                .iter()
                .enumerate()
                .for_each(|(index_into_table, fn_idx)| {
                    let ft = mod_ctx.func_types.get(fn_idx).unwrap_or_else(||panic!("FunctionType not found for index {fn_idx:?}"));
                    if ft.params.len() == bt.params.len() && ft.results.len() == bt.results.len() {
                        possible_funs.push((index_into_table, ft));
                    }

                });
            trace!("This function could possibly call {} functions", possible_funs.len());

            let caller_wasm_params = bt
                .params
                .iter()
                .flat_map(|ty| ty.to_wasm_types(fun_ctx))
                .collect::<Vec<_>>();

            trace!("Caller RichWasm Params: {:?}", bt.params); 
            trace!("Caller Wasm Params: {:?}", caller_wasm_params); 

            let caller_wasm_results = bt
                .results
                .iter()
                .flat_map(|ty| ty.to_wasm_types(fun_ctx))
                .collect::<Vec<_>>();

            trace!("Caller RichWasm Results: {:?}", bt.results); 
            trace!("Caller Wasm Results: {:?}", caller_wasm_results); 

            trace!("Now specializing the stack according to each possible function that can be called. ");

            let mut num_specialized_funcs = 0; 
            // For each possible function,
            for (count, (index_into_table, callee_ft)) in possible_funs.iter().enumerate() {

                let mut specialized_instrs = Vec::new(); 

                trace!("Specializing for {count} Function");
                // TODO: Ideally, we don't recompute this for each function and store in mod_ctx.
                let (callee_wasm_ft, callee_fun_ctx) = callee_ft.get_wasm_types();

                trace!("Callee RichWasm Params: {:?}", callee_ft.params); 
                trace!("Callee Wasm Params: {:?}", callee_wasm_ft.inputs()); 
                trace!("Tranforming to callee calling convention"); 

                // If coderef == fn_ind {
                specialized_instrs.push(temp_locals.get_local_var(coderef_idx));
                specialized_instrs.push(wasm::Instr::Const(wasm::Val::I32(*index_into_table as i32)));
                specialized_instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Eq));
                specialized_instrs.push(wasm::Instr::If(wasm::FunctionType::new(
                    &caller_wasm_params,
                    &caller_wasm_results,
                )));

                // Transform the wasm stack according to the callee calling conventions
                match crate::rwasm::FunctionType::to_callee_stack(
                    &bt.params,
                    &callee_ft.params,
                    fun_ctx,
                    &callee_fun_ctx,
                    mod_ctx,
                    &mut specialized_instrs,
                    temp_locals,
                ) {
                    Ok(_) => (),
                    Err(_) => continue,
                };
            
                specialized_instrs.push(temp_locals.get_local_var(coderef_idx));
                specialized_instrs.push(wasm::Instr::CallIndirect(
                    callee_wasm_ft,
                    wasm::Idx::<wasm::Table>::from(0_u32),
                ));

                trace!("Callee RichWasm Results: {:?}", callee_ft.results); 
                trace!("Callee Wasm Results: {:?}", callee_wasm_ft.results()); 
                trace!("Transforming according to caller calling conventions."); 

                // Transform the wasm stack according to the caller conventions
                match crate::rwasm::FunctionType::to_caller_stack(
                    &bt.results,
                    &callee_ft.results,
                    fun_ctx,
                    &callee_fun_ctx,
                    mod_ctx,
                    &mut specialized_instrs,
                    temp_locals,
                ) {
                    Ok(_) => (),
                    Err(_) => continue,
                };

                specialized_instrs.push(wasm::Instr::Else);

                num_specialized_funcs += 1;
                instrs.append(&mut specialized_instrs);
            }

            if num_specialized_funcs > 0  {
                // At the end, else { unreachable }, since we know all the functions that coderef could call statically
                instrs.push(wasm::Instr::Unreachable);
                instrs.push(wasm::Instr::End);

                // Push as many Ends as Ifs that we created.
                for _ in 0..num_specialized_funcs - 1 {
                    instrs.push(wasm::Instr::End);
                }
            }

            temp_locals.free_local_var(coderef_idx);

            for instr in &instrs{
                trace!("  {instr}");
            }
            trace!("Done translating CallIndirect Instruction");
            instrs
        }

        // variant.malloc: [t] -> [i32]
        Instr::VariantMalloc(ind, vec_pt, _qual) => {
            trace!("Translating Variant Malloc"); 

            // Variants are lowered as a pointer to heap.
            // The memory layout of variant is [ind, t*]

            // Get variant size from vec_pt by indexing using ind.
            // This gives us the _physical size_ that we need to malloc.
            let pt = vec_pt
                .get(*ind as usize)
                .unwrap_or_else(|| panic!("Failed to fetch type of variant malloc"));
            let wasm_types = pt.to_wasm_types(fun_ctx);

            let mut instrs = Vec::new();

            // Malloc size of the type + 32 (ind)
            let variant_size = pt.to_u32(fun_ctx) as i32;
            instrs.push(wasm::Instr::Const(wasm::Val::I32(variant_size)));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(32)));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
            instrs.push(mod_ctx.malloc.clone());

            // Save variant pointer in a temporary variable since we have to return it.
            let variant_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.set_local_var(variant_ptr));

            // Store ind at the variant pointer
            instrs.push(temp_locals.get_local_var(variant_ptr));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(*ind as i32)));
            instrs.push(store(ValType::I32));

            // Initialize a working pointer to the end of the variant (we're working backwards)
            let working_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.get_local_var(variant_ptr));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(variant_size)));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(32)));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
            instrs.push(temp_locals.set_local_var(working_ptr));

            // Store the values on the heap at malloc.
            for wasm_ty in wasm_types.iter().rev() {
                // Update val working pointer by subtracting size of the type.
                instrs.push(temp_locals.get_local_var(working_ptr));
                instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
                instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                instrs.push(temp_locals.set_local_var(working_ptr));

                // Store data in temp variable
                let data = temp_locals.get_new_local_var(*wasm_ty);
                instrs.push(temp_locals.set_local_var(data));

                // Load ptr, load data, store value
                instrs.push(temp_locals.get_local_var(working_ptr));
                instrs.push(temp_locals.get_local_var(data));
                instrs.push(store(*wasm_ty));

                temp_locals.free_local_var(data);
            }

            temp_locals.free_local_var(working_ptr);

            // Return variant pointer
            instrs.push(temp_locals.get_local_var(variant_ptr));
            temp_locals.free_local_var(variant_ptr);

            for instr in &instrs {
                trace!("  {instr}"); 
            }

            instrs
        }

        // variant.case : [t*, i32 (pointer)] -> [t*, (i32)?]
        Instr::VariantCase(qual, ty, bt, _le, bodies) => {
            trace!("Translating Variant Case");
            
            let mut instrs = Vec::new();

            // Save the pointer
            let variant_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.set_local_var(variant_ptr));

            // Initialize working pointer as variant ptr + 32
            let working_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.get_local_var(variant_ptr));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(32)));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
            instrs.push(temp_locals.set_local_var(working_ptr));

            // For num_blocks = 3
            // block { block { block { block { br_table [0 1 2] 3}; body0; br 3}; body1; br 2}; body2; br 1} br 0}
            let num_blocks = bodies.len();

            // Put each case of the variant case in its own block (with the same block type)
            let (params, results) = bt.get_wasm_types(fun_ctx);
            let blocktype = FunctionType::new(&params, &results);

            // block { block { block { block {
            instrs.append(&mut vec![wasm::Instr::Block(blocktype); num_blocks]);
            // The innermost block is a default block that just has a break out of it
            instrs.push(wasm::Instr::Block(blocktype));
            
            // Generate default values for all the return types 
            for result in &results {
                instrs.push(match result {
                    ValType::I32 => wasm::Instr::Const(wasm::Val::I32(0)),
                    ValType::I64 => wasm::Instr::Const(wasm::Val::I64(0)),
                    ValType::F32 => wasm::Instr::Const(wasm::Val::F32(ordered_float::OrderedFloat(0.0))),
                    ValType::F64 => wasm::Instr::Const(wasm::Val::F64(ordered_float::OrderedFloat(0.0))),
                })
            }

            // Go to pointer, i32.load the index for the variant case and put on stack
            instrs.push(temp_locals.get_local_var(variant_ptr));
            instrs.push(load(ValType::I32));

            // br_table [0 1 2] 3};
            let br_table_labels: Vec<wasm::Label> = (0..num_blocks)
                .map(|s| wasm::Label::from(s as u32))
                .collect();
            instrs.push(wasm::Instr::BrTable {
                table: br_table_labels,
                default: wasm::Label::from(num_blocks),
            });
            
            // End the block containing the br_table 
            instrs.push(wasm::Instr::End);

            let num_bodies = bodies.len();
            for ((body_num, body), stack_ty) in bodies.iter().enumerate().zip(ty.iter()) {
                
                trace!("for case {body_num}, this is our body {body:?} and this is our stack_ty {stack_ty:?}");
                
                // Read from the heap according to stack type expected
                for wasm_ty in stack_ty.to_wasm_types(fun_ctx) {
                    // Load from heap
                    instrs.push(temp_locals.get_local_var(working_ptr));
                    instrs.push(load(wasm_ty));
                    
                    // Update working pointer
                    instrs.push(temp_locals.get_local_var(working_ptr));
                    instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(wasm_ty))));
                    instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                    instrs.push(temp_locals.set_local_var(working_ptr));
                }

                // Translate the body
                instrs.append(
                    &mut body
                        .iter()
                        .flat_map(|instr| translate_instr(instr, fun_ctx, mod_ctx, temp_locals))
                        .collect(),
                );

                instrs.push(wasm::Instr::Br(wasm::Label::from(num_bodies - body_num -1)));
                instrs.push(wasm::Instr::End);
            }

            // Note that the qualifier on a variant case instruction will determine
            // whether the variant is freed or not (linear=free). In typechecking
            // CapWasm programs it is always possible to determine whether this is
            // unrestricted or linear at compile time
            //
            // If Qual GC -> return pointer and block returns
            // If Qual Lin -> free the underlying memory, return whatever the block returns

            let qual = match qual {
                Qual::Var(ind) => fun_ctx.qual_closure[&ind.0],
                Qual::Lin => QualConst::Lin,
                Qual::GC => QualConst::GC,
            };

            match qual {
                QualConst::Lin => {
                    instrs.push(temp_locals.get_local_var(variant_ptr));
                    instrs.push(mod_ctx.free.clone());
                }
                QualConst::GC => {
                    // The stack returned by Variant Case with the GC/Unr Qual is 
                    // [variant_ptr, everything returned by variant] <- TOS
                    // So we have to save expected results in local variables, load the variant pointer and then load expected results. 

                    let mut results_in_rev = vec![]; 
                    for wasm_ty in results.iter().rev() {
                        let res = temp_locals.get_new_local_var(*wasm_ty);
                        instrs.push(temp_locals.set_local_var(res));    
                        results_in_rev.push(res);
                    }
                    instrs.push(temp_locals.get_local_var(variant_ptr));
                    for res in results_in_rev.iter().rev() {
                        instrs.push(temp_locals.get_local_var(*res));
                        temp_locals.free_local_var(*res);                           
                    }
                }
            }

            temp_locals.free_local_var(variant_ptr);
            trace!("Variant Case instructions");
            for instr in &instrs {
                trace!("  {instr}")
            }
            trace!("end of variant case");
            instrs
        }

        // exist.pack : [t*] -> [i32]
        Instr::ExistPack(pt, ht, _qual) => {
            trace!("Translating Exists Pack");

            let mut instrs = Vec::new();

            // The stack shape has to conform to the shape in the heaptype.
            // The caller is the shape of the stack with type variables instantiated with pretype.
            // The callee is the shape of the stack with type variables uninstantiated.

            let callee_params = match ht {
                HeapType::Variant(_) | HeapType::Struct(_) | HeapType::Array(_) => {
                    panic!("Found Variant/Struct/Array HeapType when trying to fetch callee_params for ExistPack. Should only have found an Exists.")
                }
                HeapType::Exists(_, _, ty) => ty.clone(),
            };

            
            let mut ty_var_map = HashMap::new();
            ty_var_map.insert(0, pt.clone());
            
            let caller_params = callee_params.instantiate_ty(&ty_var_map);

            trace!("CALLER PARAMS: {caller_params:?}");
            trace!("CALLEE PARAMS: {callee_params:?}");

            match crate::rwasm::FunctionType::to_callee_stack(
                &[caller_params],
                &[callee_params.clone()],
                fun_ctx,
                &FunctionContext::create_empty(),
                mod_ctx,
                &mut instrs,
                temp_locals,
            ) {
                Ok(_) => (),
                Err(e) => panic!("{e}"),
            };

            // Get size of callee params and malloc            
            let size = callee_params.to_u32(fun_ctx) as i32;
            trace!("Size of pretype of malloc: {size}");
            trace!("{}",wasm::Instr::Const(wasm::Val::I32(size)));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(size)));
            instrs.push(mod_ctx.malloc.clone());

            // Save pointer
            let ex_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.set_local_var(ex_ptr));

            // Initialize working pointer to the end of the ex_ptr
            let working_ptr = temp_locals.get_new_local_var(ValType::I32);
            let get_working_ptr = temp_locals.get_local_var(working_ptr);
            let set_working_ptr = temp_locals.set_local_var(working_ptr);
            instrs.push(temp_locals.get_local_var(ex_ptr));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(size)));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
            instrs.push(temp_locals.set_local_var(working_ptr));

            // Store t* at pointer
            for wasm_ty in callee_params.to_wasm_types(fun_ctx).iter().rev() {
                trace!("Storing {wasm_ty} at heap for ex ptr");

                // Update the working pointer to be pointer - size of type
                instrs.push(get_working_ptr.clone());
                instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
                instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
                instrs.push(set_working_ptr.clone());

                // store [ptr data] -> []
                // Data is already on the stack so pop, save in temporary variable.
                let data = temp_locals.get_new_local_var(*wasm_ty);
                instrs.push(temp_locals.set_local_var(data));

                // Push working pointer, push data and do appropriate store
                instrs.push(get_working_ptr.clone());
                instrs.push(temp_locals.get_local_var(data));
                instrs.push(store(*wasm_ty));

                temp_locals.free_local_var(data);
            }
            temp_locals.free_local_var(working_ptr);

            // Return pointer
            instrs.push(temp_locals.get_local_var(ex_ptr));
            temp_locals.free_local_var(ex_ptr);

            trace!("Translation of Exists pack");
            for instr in &instrs {
                trace!("  {instr}");
            }
            trace!("Ending Translation of Exists pack");

            instrs
        }

        // [t*, i32] -> [t*, i32?]
        Instr::ExistUnpack(qual, bt, _le, body, pt) => {
            trace!("Translating Exist unpack");
            let mut instrs = Vec::new();

            // Save the pointer
            let ex_ptr = temp_locals.get_new_local_var(ValType::I32);
            instrs.push(temp_locals.set_local_var(ex_ptr));

            let params = bt.params
                .iter()
                .flat_map(|p| p.to_wasm_types(fun_ctx))
                .collect::<Vec<_>>(); 
            let results = bt.results
                .iter()
                .flat_map(|p| p.to_wasm_types(fun_ctx))
                .collect::<Vec<_>>();

            instrs.push(wasm::Instr::Block(FunctionType::new(params.as_slice(), results.as_slice())));

            // Initialize working pointer to the start of the ex_ptr
            let working_ptr = temp_locals.get_new_local_var(ValType::I32);
            let get_working_ptr = temp_locals.get_local_var(working_ptr);
            let set_working_ptr = temp_locals.set_local_var(working_ptr);
            instrs.push(temp_locals.get_local_var(ex_ptr));
            instrs.push(temp_locals.set_local_var(working_ptr));

            // Load from pointer
            for wasm_ty in pt.to_wasm_types(fun_ctx).iter() {
                // load [ptr] -> [data]
                // Data is already on the stack so pop, save in temporary variable.
                instrs.push(get_working_ptr.clone());
                instrs.push(load(*wasm_ty));

                // Update the working pointer to be pointer + size of type
                instrs.push(get_working_ptr.clone());
                instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
                instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
                instrs.push(set_working_ptr.clone());

                trace!("laoding {wasm_ty}");
            }

            // Translate the body
            instrs.append(
                &mut body
                    .iter()
                    .flat_map(|instr| translate_instr(instr, fun_ctx, mod_ctx, temp_locals))
                    .collect::<Vec<_>>(),
            );

            temp_locals.free_local_var(working_ptr);

            instrs.push(wasm::Instr::End);

            // If Qual GC -> return pointer and block returns
            // If Qual Lin -> free the underlying memory, return whatever the block returns

            let qual = match qual {
                Qual::Var(ind) => fun_ctx.qual_closure[&ind.0],
                Qual::Lin => QualConst::Lin,
                Qual::GC => QualConst::GC,
            };

            match qual {
                QualConst::Lin => {
                    instrs.push(temp_locals.get_local_var(ex_ptr));
                    instrs.push(mod_ctx.free.clone());
                }
                QualConst::GC => {
                    // The stack returned by Exists Unpack with the GC/Unr Qual is 
                    // [variant_ptr, everything returned by variant] <- TOS
                    // So we have to save expected results in local variables, load the variant pointer and then load expected results. 

                    let mut results_in_rev = vec![]; 
                    for wasm_ty in results.iter().rev() {
                        let res = temp_locals.get_new_local_var(*wasm_ty);
                        instrs.push(temp_locals.set_local_var(res));    
                        results_in_rev.push(res);
                    }
                    instrs.push(temp_locals.get_local_var(ex_ptr));
                    for res in results_in_rev.iter().rev() {
                        instrs.push(temp_locals.get_local_var(*res));
                        temp_locals.free_local_var(*res);                           
                    }
                }
            }

            temp_locals.free_local_var(ex_ptr);

            instrs
        }

        Instr::Global(op, idx) => {
            trace!("Translating Global {op:?} for idx{idx:?}");
            
            let _type = mod_ctx
                .rwasm_global_types
                .get(idx)
                .expect("Each RichWasm Global Index should be mapped to its type");
            trace!("Global Rwasm Type: {:?}", _type);

            let ty_size = _type.to_wasm_types(fun_ctx);
            let wasm_types = mod_ctx.wasm_global_types
                .get(idx)
                .unwrap_or_else(||panic!("Expected global at index {idx} but did not find."));
            let wasm_globals = &mod_ctx.get_wasm_global_list(*idx);
            trace!("Wasm Global Types {:?}", mod_ctx.wasm_global_types);
            trace!("Global Wasm Type: {:?}", wasm_types);

            let instrs = match op {
                GlobalOp::Get => resolve_get_operations(false, wasm_types, &ty_size, wasm_globals),

                GlobalOp::Set => {
                    resolve_set_operations(false, wasm_types, &ty_size, wasm_globals, temp_locals)
                }
            }; 

            trace!("Global op Instrs produced: ");
            for instr in &instrs {
                trace!("  {instr}");
            }
            instrs
        }

        Instr::Local(op, ind) => {
            trace!("Translating Local Ops");

            let wasm_locals = &fun_ctx.get_wasm_local_list(*ind);
            let wasm_local_types = &fun_ctx.wasm_local_types[ind];

            match op {
                LocalOp::Get(_qual, pt) => {
                    trace!("\nTranslation of local.get({ind})");
                    
                    let instrs = resolve_get_operations(
                    true,
                    wasm_local_types,
                    &pt.to_wasm_types(fun_ctx),
                    wasm_locals,
                    ); 

                    for instr in &instrs {
                        trace!("  {instr}");
                    }

                    instrs
                }
                ,

                LocalOp::Set(ty) => {
                    // The stack types will be in reverse of what the local type is.
                    let stack_ty = &mut ty.to_wasm_types(fun_ctx);
                    stack_ty.reverse();
                    
                    trace!("\nTranslation of local.set({ind})");
                    trace!("Stack type: {stack_ty:?}");                    
                    trace!("Wasm Local type: {wasm_local_types:?}");

                    let instrs = resolve_set_operations(
                        true,
                        wasm_local_types,
                        stack_ty,
                        wasm_locals,
                        temp_locals,
                    ); 
                    
                    for instr in &instrs {
                        trace!("  {instr}");
                    }
                    
                    trace!("End of Translation of local.set({ind})\n");


                    instrs
                }

                LocalOp::Tee(ty) => {
                    // Set followed by a get.
                    let mut instrs = Vec::new();

                    // The stack types will be in reverse of what the local type is.
                    let stack_ty = &mut ty.to_wasm_types(fun_ctx);
                    stack_ty.reverse();

                    instrs.append(&mut resolve_set_operations(
                        true,
                        wasm_local_types,
                        stack_ty,
                        wasm_locals,
                        temp_locals,
                    ));
                    instrs.append(&mut resolve_get_operations(
                        true,
                        wasm_local_types,
                        &ty.get_pt().to_wasm_types(fun_ctx),
                        wasm_locals,
                    ));
                    instrs
                }
            }
        }

        // Effectively erased. Erase local effects and convert to a block.
        Instr::MemUnpack(bt, _le, body, ty) => {
            trace!("Translating MemUnpack");


            let mut params = vec![];
            let mut type_being_unpacked = (*ty.0).to_wasm_types(fun_ctx); 
            params.append(&mut type_being_unpacked); 

            let (mut old_params, results) = bt.get_wasm_types(fun_ctx);
            params.append(&mut old_params);

            let block_ty = wasm::FunctionType::new(&params, &results);
            trace!("block type: {block_ty}");

            let mut instrs = vec![wasm::Instr::Block(wasm::FunctionType::new(
                &params, &results,
            ))];
            instrs.append(
                &mut body
                    .iter()
                    .flat_map(|inst| translate_instr(inst, fun_ctx, mod_ctx, temp_locals))
                    .collect(),
            );
            instrs.push(wasm::Instr::End);
            instrs
        }

        /* Erased */
        Instr::Unit
        | Instr::RecFold(_)
        | Instr::RecUnfold
        | Instr::Group(_, _)
        | Instr::UnGroup
        | Instr::CapSplit
        | Instr::CapJoin
        | Instr::RefDemote
        | Instr::MemPack(_)
        | Instr::RefSplit
        | Instr::RefJoin
        | Instr::Qualify(_) => vec![],

        /* Identical */
        Instr::Unreachable => vec![wasm::Instr::Unreachable],
        Instr::Nop => vec![wasm::Instr::Nop],
        Instr::Drop(pt) => {
            match pt {
                PreType::Unit => vec![],
                _ => vec![wasm::Instr::Drop],
            }            
        },
        Instr::Select => vec![wasm::Instr::Select],
        Instr::Return => vec![wasm::Instr::Return],
        Instr::Br(lab) => vec![wasm::Instr::Br(wasm::Label::from(*lab))],
        Instr::BrIf(lab) => vec![wasm::Instr::BrIf(wasm::Label::from(*lab))],
        Instr::BrTable(default, table) => {
            vec![wasm::Instr::BrTable {
                table: table.iter().map(|lab| wasm::Label::from(*lab)).collect(),
                default: wasm::Label::from(*default),
            }]
        }
        Instr::Constant(cty, c) => vec![wasm::Instr::Const(match cty {
            ConstType::I32(_) => wasm::Val::I32(*c as i32),
            ConstType::I64(_) => wasm::Val::I64(*c as i64),
            ConstType::F32 => wasm::Val::F32(ordered_float::OrderedFloat(*c as f32)),
            ConstType::F64 => wasm::Val::F64(ordered_float::OrderedFloat(*c as f64)),
        })],

        Instr::Numeric(num_instr) => match num_instr {
            NumericInstr::Unary(un_instr) => vec![wasm::Instr::Unary(match un_instr {
                UnaryOp::I32Eqz => wasm::UnaryOp::I32Eqz,
                UnaryOp::I64Eqz => wasm::UnaryOp::I64Eqz,
                UnaryOp::I32Clz => wasm::UnaryOp::I32Clz,
                UnaryOp::I32Ctz => wasm::UnaryOp::I32Ctz,
                UnaryOp::I32Popcnt => wasm::UnaryOp::I32Popcnt,
                UnaryOp::I64Clz => wasm::UnaryOp::I64Clz,
                UnaryOp::I64Ctz => wasm::UnaryOp::I64Ctz,
                UnaryOp::I64Popcnt => wasm::UnaryOp::I64Popcnt,
                UnaryOp::F32Abs => wasm::UnaryOp::F32Abs,
                UnaryOp::F32Neg => wasm::UnaryOp::F32Neg,
                UnaryOp::F32Ceil => wasm::UnaryOp::F32Ceil,
                UnaryOp::F32Floor => wasm::UnaryOp::F32Floor,
                UnaryOp::F32Trunc => wasm::UnaryOp::F32Trunc,
                UnaryOp::F32Nearest => wasm::UnaryOp::F32Nearest,
                UnaryOp::F32Sqrt => wasm::UnaryOp::F32Sqrt,
                UnaryOp::F64Abs => wasm::UnaryOp::F64Abs,
                UnaryOp::F64Neg => wasm::UnaryOp::F64Neg,
                UnaryOp::F64Ceil => wasm::UnaryOp::F64Ceil,
                UnaryOp::F64Floor => wasm::UnaryOp::F64Floor,
                UnaryOp::F64Trunc => wasm::UnaryOp::F64Trunc,
                UnaryOp::F64Nearest => wasm::UnaryOp::F64Nearest,
                UnaryOp::F64Sqrt => wasm::UnaryOp::F64Sqrt,
                UnaryOp::I32WrapI64 => wasm::UnaryOp::I32WrapI64,
                UnaryOp::I32TruncF32S => wasm::UnaryOp::I32TruncF32S,
                UnaryOp::I32TruncF32U => wasm::UnaryOp::I32TruncF32U,
                UnaryOp::I32TruncF64S => wasm::UnaryOp::I32TruncF64S,
                UnaryOp::I32TruncF64U => wasm::UnaryOp::I32TruncF64U,
                UnaryOp::I64ExtendI32S => wasm::UnaryOp::I64ExtendI32S,
                UnaryOp::I64ExtendI32U => wasm::UnaryOp::I64ExtendI32U,
                UnaryOp::I64TruncF32S => wasm::UnaryOp::I64TruncF32S,
                UnaryOp::I64TruncF32U => wasm::UnaryOp::I64TruncF32U,
                UnaryOp::I64TruncF64S => wasm::UnaryOp::I64TruncF64S,
                UnaryOp::I64TruncF64U => wasm::UnaryOp::I64TruncF64U,
                UnaryOp::F32ConvertI32S => wasm::UnaryOp::F32ConvertI32S,
                UnaryOp::F32ConvertI32U => wasm::UnaryOp::F32ConvertI32U,
                UnaryOp::F32ConvertI64S => wasm::UnaryOp::F32ConvertI64S,
                UnaryOp::F32ConvertI64U => wasm::UnaryOp::F32ConvertI64U,
                UnaryOp::F32DemoteF64 => wasm::UnaryOp::F32DemoteF64,
                UnaryOp::F64ConvertI32S => wasm::UnaryOp::F64ConvertI32S,
                UnaryOp::F64ConvertI32U => wasm::UnaryOp::F64ConvertI32U,
                UnaryOp::F64ConvertI64S => wasm::UnaryOp::F64ConvertI64S,
                UnaryOp::F64ConvertI64U => wasm::UnaryOp::F64ConvertI64U,
                UnaryOp::F64PromoteF32 => wasm::UnaryOp::F64PromoteF32,
                UnaryOp::I32ReinterpretF32 => wasm::UnaryOp::I32ReinterpretF32,
                UnaryOp::I64ReinterpretF64 => wasm::UnaryOp::I64ReinterpretF64,
                UnaryOp::F32ReinterpretI32 => wasm::UnaryOp::F32ReinterpretI32,
                UnaryOp::F64ReinterpretI64 => wasm::UnaryOp::F64ReinterpretI64,
            })],

            NumericInstr::Binary(bin_instr) => {
                vec![wasm::Instr::Binary(match bin_instr {
                    BinaryOp::I32Eq => wasm::BinaryOp::I32Eq,
                    BinaryOp::I32Ne => wasm::BinaryOp::I32Ne,
                    BinaryOp::I32LtS => wasm::BinaryOp::I32LtS,
                    BinaryOp::I32LtU => wasm::BinaryOp::I32LtU,
                    BinaryOp::I32GtS => wasm::BinaryOp::I32GtS,
                    BinaryOp::I32GtU => wasm::BinaryOp::I32GtU,
                    BinaryOp::I32LeS => wasm::BinaryOp::I32LeS,
                    BinaryOp::I32LeU => wasm::BinaryOp::I32LeU,
                    BinaryOp::I32GeS => wasm::BinaryOp::I32GeS,
                    BinaryOp::I32GeU => wasm::BinaryOp::I32GeU,
                    BinaryOp::I64Eq => wasm::BinaryOp::I64Eq,
                    BinaryOp::I64Ne => wasm::BinaryOp::I64Ne,
                    BinaryOp::I64LtS => wasm::BinaryOp::I64LtS,
                    BinaryOp::I64LtU => wasm::BinaryOp::I64LtU,
                    BinaryOp::I64GtS => wasm::BinaryOp::I64GtS,
                    BinaryOp::I64GtU => wasm::BinaryOp::I64GtU,
                    BinaryOp::I64LeS => wasm::BinaryOp::I64LeS,
                    BinaryOp::I64LeU => wasm::BinaryOp::I64LeU,
                    BinaryOp::I64GeS => wasm::BinaryOp::I64GeS,
                    BinaryOp::I64GeU => wasm::BinaryOp::I64GeU,
                    BinaryOp::F32Eq => wasm::BinaryOp::F32Eq,
                    BinaryOp::F32Ne => wasm::BinaryOp::F32Ne,
                    BinaryOp::F32Lt => wasm::BinaryOp::F32Lt,
                    BinaryOp::F32Gt => wasm::BinaryOp::F32Gt,
                    BinaryOp::F32Le => wasm::BinaryOp::F32Le,
                    BinaryOp::F32Ge => wasm::BinaryOp::F32Ge,
                    BinaryOp::F64Eq => wasm::BinaryOp::F64Eq,
                    BinaryOp::F64Ne => wasm::BinaryOp::F64Ne,
                    BinaryOp::F64Lt => wasm::BinaryOp::F64Lt,
                    BinaryOp::F64Gt => wasm::BinaryOp::F64Gt,
                    BinaryOp::F64Le => wasm::BinaryOp::F64Le,
                    BinaryOp::F64Ge => wasm::BinaryOp::F64Ge,
                    BinaryOp::I32Add => wasm::BinaryOp::I32Add,
                    BinaryOp::I32Sub => wasm::BinaryOp::I32Sub,
                    BinaryOp::I32Mul => wasm::BinaryOp::I32Mul,
                    BinaryOp::I32DivS => wasm::BinaryOp::I32DivS,
                    BinaryOp::I32DivU => wasm::BinaryOp::I32DivU,
                    BinaryOp::I32RemS => wasm::BinaryOp::I32RemS,
                    BinaryOp::I32RemU => wasm::BinaryOp::I32RemU,
                    BinaryOp::I32And => wasm::BinaryOp::I32And,
                    BinaryOp::I32Or => wasm::BinaryOp::I32Or,
                    BinaryOp::I32Xor => wasm::BinaryOp::I32Xor,
                    BinaryOp::I32Shl => wasm::BinaryOp::I32Shl,
                    BinaryOp::I32ShrS => wasm::BinaryOp::I32ShrS,
                    BinaryOp::I32ShrU => wasm::BinaryOp::I32ShrU,
                    BinaryOp::I32Rotl => wasm::BinaryOp::I32Rotl,
                    BinaryOp::I32Rotr => wasm::BinaryOp::I32Rotr,
                    BinaryOp::I64Add => wasm::BinaryOp::I64Add,
                    BinaryOp::I64Sub => wasm::BinaryOp::I64Sub,
                    BinaryOp::I64Mul => wasm::BinaryOp::I64Mul,
                    BinaryOp::I64DivS => wasm::BinaryOp::I64DivS,
                    BinaryOp::I64DivU => wasm::BinaryOp::I64DivU,
                    BinaryOp::I64RemS => wasm::BinaryOp::I64RemS,
                    BinaryOp::I64RemU => wasm::BinaryOp::I64RemU,
                    BinaryOp::I64And => wasm::BinaryOp::I64And,
                    BinaryOp::I64Or => wasm::BinaryOp::I64Or,
                    BinaryOp::I64Xor => wasm::BinaryOp::I64Xor,
                    BinaryOp::I64Shl => wasm::BinaryOp::I64Shl,
                    BinaryOp::I64ShrS => wasm::BinaryOp::I64ShrS,
                    BinaryOp::I64ShrU => wasm::BinaryOp::I64ShrU,
                    BinaryOp::I64Rotl => wasm::BinaryOp::I64Rotl,
                    BinaryOp::I64Rotr => wasm::BinaryOp::I64Rotr,
                    BinaryOp::F32Add => wasm::BinaryOp::F32Add,
                    BinaryOp::F32Sub => wasm::BinaryOp::F32Sub,
                    BinaryOp::F32Mul => wasm::BinaryOp::F32Mul,
                    BinaryOp::F32Div => wasm::BinaryOp::F32Div,
                    BinaryOp::F32Min => wasm::BinaryOp::F32Min,
                    BinaryOp::F32Max => wasm::BinaryOp::F32Max,
                    BinaryOp::F32Copysign => wasm::BinaryOp::F32Copysign,
                    BinaryOp::F64Add => wasm::BinaryOp::F64Add,
                    BinaryOp::F64Sub => wasm::BinaryOp::F64Sub,
                    BinaryOp::F64Mul => wasm::BinaryOp::F64Mul,
                    BinaryOp::F64Div => wasm::BinaryOp::F64Div,
                    BinaryOp::F64Min => wasm::BinaryOp::F64Min,
                    BinaryOp::F64Max => wasm::BinaryOp::F64Max,
                    BinaryOp::F64Copysign => wasm::BinaryOp::F64Copysign,
                })]
            }
        },
    }
}
