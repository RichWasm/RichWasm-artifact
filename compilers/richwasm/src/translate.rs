use crate::translate_insts::{load, store};
use crate::*;
use crate::{rwasm::*, translate_insts::get_size};
use std::{
    cmp::{max, min},
    collections::HashMap,
    marker::PhantomData,
};
use translate_insts::{FunctionContext, ModuleContext, TempLocals};
use wasabi_wasm as wasm;

// General transitive closure function used to get transitive closure of Qual and Size variables.
// Get the transitive closure of [T] where T can be a variable.
// You have to pass in the closure constructed thus far and a comparison function to be able to reslove variables.
fn trans_closure<T: std::fmt::Debug + ResolveVariable<R>, R: Copy + std::fmt::Debug + Default>(
    t_list: &[T],
    closure: &HashMap<u32, R>,
    comp: fn(R, R) -> R,
) -> R {
    let default_val_of_type: R = Default::default();
    t_list
        .iter()
        .map(|t| t.resolve_vars(closure, comp))
        .fold(default_val_of_type, comp)
}

impl FunctionContext {
    pub(crate) fn create_empty() -> Self {
        FunctionContext {
            typevar_size: HashMap::new(),
            size_closure: HashMap::new(),
            qual_closure: HashMap::new(),
            wasm_local_types: HashMap::new(),
            local_map: HashMap::new(),
        }
    }

    pub(crate) fn get_qual_closure(
        qual_bounds: &HashMap<u32, (Vec<Qual>, Vec<Qual>)>,
    ) -> HashMap<u32, QualConst> {
        let mut qual_closure: HashMap<u32, QualConst> = HashMap::new();
        let mut qual_upper_closure: HashMap<u32, QualConst> = HashMap::new();
        let mut qual_lower_closure: HashMap<u32, QualConst> = HashMap::new();

        for (ind, (upper, lower)) in qual_bounds {
            let upper = trans_closure::<Qual, QualConst>(upper, &qual_upper_closure, min);
            qual_upper_closure.insert(*ind, upper);

            let lower = trans_closure::<Qual, QualConst>(lower, &qual_lower_closure, max);
            qual_lower_closure.insert(*ind, lower);

            qual_closure.insert(
                *ind,
                match (upper, lower) {
                    (QualConst::GC, _) => QualConst::GC,
                    (_, QualConst::Lin) => QualConst::Lin,
                    (QualConst::Lin, QualConst::GC) => {
                        panic!("Tried to compare QualConst::Lin and QualConst::GC")
                    }
                },
            );
        }

        qual_closure
    }

    pub(crate) fn get_size_closure(
        size_bounds: &HashMap<u32, (Vec<Size>, Vec<Size>)>,
    ) -> HashMap<u32, u32> {
        let mut size_closure: HashMap<u32, u32> = HashMap::new();
        let mut trans_closure_upper: HashMap<u32, SizeConst> = HashMap::new();
        let mut trans_closure_lower: HashMap<u32, SizeConst> = HashMap::new();

        // We have to go in order of variable declaration.
        for var in 0..size_bounds.len() {
            let var = &(var as u32);
            let (upper, lower) = size_bounds.get(var).unwrap();

            // For upper bounds,
            //   If there exists atleast one concrete value, take the smallest concrete value
            //   If all of them are abstract, it is unknown (None)
            let upper = trans_closure::<Size, SizeConst>(upper, &trans_closure_upper, min);
            trans_closure_upper.insert(*var, upper);

            // For lower bounds,
            //   If there exists atleast one concrete value, take the largest concrete value
            //   If all of them are abstract, it is unknown (None)
            let lower = trans_closure::<Size, SizeConst>(lower, &trans_closure_lower, max);
            trans_closure_lower.insert(*var, lower);

            size_closure.insert(
                *var,
                match (&upper, &lower) {
                    (SizeConst::Unknown, SizeConst::Unknown) => 32, // TypeVar is Boxed
                    (SizeConst::Unknown, SizeConst::Known(lower)) => max(*lower, 32), // TypeVar is boxed
                    (SizeConst::Known(upper), SizeConst::Unknown) => *upper,
                    (SizeConst::Known(upper), SizeConst::Known(_lower)) => *upper,
                },
            );
        }

        size_closure
    }
}

// Trait to standardize how we resolve type/qual/etc variables.
// Pass in the Concrete version of the type we are resolving.
// You have to provide bounds information on the variables.
// You also have to provide a comparison function to be able to compare between the concrete versions.
trait ResolveVariable<T> {
    fn resolve_vars(&self, bounds: &HashMap<u32, T>, comp: fn(T, T) -> T) -> T;
}

impl ResolveVariable<QualConst> for Qual {
    fn resolve_vars(
        &self,
        qual_var_bounds: &HashMap<u32, QualConst>,
        _comp: fn(QualConst, QualConst) -> QualConst,
    ) -> QualConst {
        match self {
            Qual::Var(ind) => qual_var_bounds[&ind.0],
            Qual::Lin => QualConst::Lin,
            Qual::GC => QualConst::GC,
        }
    }
}

impl ResolveVariable<SizeConst> for Size {
    fn resolve_vars(
        &self,
        bounds: &HashMap<u32, SizeConst>,
        comp: fn(SizeConst, SizeConst) -> SizeConst,
    ) -> SizeConst {
        match self {
            // We make the assumption that variables are declared before they are referenced.
            Size::Concrete(c) => SizeConst::Known(*c),
            Size::Abstract(var) => bounds[&var.0],
            Size::Plus(s1, s2) => {
                let s1 = trans_closure::<Size, SizeConst>(&[*s1.clone()], bounds, comp);
                let s2 = trans_closure::<Size, SizeConst>(&[*s2.clone()], bounds, comp);
                // If one of the sizes is abstract (None), the Plus is abstract (None)
                match (s1, s2) {
                    (SizeConst::Known(c1), SizeConst::Known(c2)) => SizeConst::Known(c1 + c2),
                    (SizeConst::Known(_), SizeConst::Unknown)
                    | (SizeConst::Unknown, SizeConst::Known(_))
                    | (SizeConst::Unknown, SizeConst::Unknown) => SizeConst::Unknown,
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum SizeConst {
    Known(u32),
    Unknown,
}

impl Default for SizeConst {
    fn default() -> Self {
        Self::Unknown
    }
}

impl Ord for SizeConst {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (SizeConst::Known(c1), SizeConst::Known(c2)) => c1.cmp(c2),
            (SizeConst::Known(_), SizeConst::Unknown) => std::cmp::Ordering::Less,
            (SizeConst::Unknown, SizeConst::Known(_)) => std::cmp::Ordering::Greater,
            (SizeConst::Unknown, SizeConst::Unknown) => std::cmp::Ordering::Equal,
        }
    }
}

impl PartialOrd for SizeConst {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(match (self, other) {
            (SizeConst::Known(c1), SizeConst::Known(c2)) => c1.cmp(c2),
            (SizeConst::Known(_), SizeConst::Unknown) => std::cmp::Ordering::Greater,
            (SizeConst::Unknown, SizeConst::Known(_)) => std::cmp::Ordering::Less,
            (SizeConst::Unknown, SizeConst::Unknown) => std::cmp::Ordering::Equal,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum QualConst {
    Lin,
    GC,
}

impl Default for QualConst {
    fn default() -> Self {
        Self::GC
    }
}

impl Ord for QualConst {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (QualConst::Lin, QualConst::Lin) => std::cmp::Ordering::Equal,
            (QualConst::Lin, QualConst::GC) => std::cmp::Ordering::Greater,
            (QualConst::GC, QualConst::Lin) => std::cmp::Ordering::Less,
            (QualConst::GC, QualConst::GC) => std::cmp::Ordering::Less,
        }
    }
}

impl PartialOrd for QualConst {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(match (self, other) {
            (QualConst::Lin, QualConst::Lin) => std::cmp::Ordering::Equal,
            (QualConst::Lin, QualConst::GC) => std::cmp::Ordering::Greater,
            (QualConst::GC, QualConst::Lin) => std::cmp::Ordering::Less,
            (QualConst::GC, QualConst::GC) => std::cmp::Ordering::Less,
        })
    }
}

impl Type {
    pub(crate) fn to_wasm_types(&self, fun_ctx: &FunctionContext) -> Vec<wasm::ValType> {
        let pt = self.get_pt();
        pt.to_wasm_types(fun_ctx)
    }

    pub(crate) fn to_size(&self, type_variable_sizes: &HashMap<u32, Size>) -> Size {
        let pt = self.get_pt();
        pt.to_size(type_variable_sizes)
    }

    pub(crate) fn to_u32(&self, fun_ctx: &FunctionContext) -> u32 {
        self.to_size(&fun_ctx.typevar_size)
            .to_u32(&fun_ctx.size_closure)
    }

    pub(crate) fn instantiate_ty(&self, ty_var_map: &HashMap<u32, PreType>) -> Type {
        match self.get_pt() {
            PreType::Var(ty_var) => {
                let y = ty_var_map
                    .get(&ty_var.0)
                    .unwrap_or_else(|| panic!("Typevar {ty_var:?} has not been instantiated."));

                trace!("VAR INST: {y:?}");
                Type(Box::new(y.clone()), self.1.clone())
            }

            PreType::Product(vec_ty) => {
                let mut tys = Vec::new();
                for ty in vec_ty {
                    let inst_ty = ty.instantiate_ty(ty_var_map);
                    trace!("PROD_TY: {inst_ty:?}");
                    tys.push(inst_ty);
                }
                Type(Box::new(PreType::Product(tys)), self.1.clone())
            }

            PreType::CodeRef(ty) => {
                let i_ft_p = ty
                    .params
                    .iter()
                    .map(|ty| ty.instantiate_ty(ty_var_map))
                    .collect::<Vec<_>>();
                let i_ft_r = ty
                    .results
                    .iter()
                    .map(|ty| ty.instantiate_ty(ty_var_map))
                    .collect::<Vec<_>>();

                Type(
                    Box::new(PreType::CodeRef(rwasm::FunctionType {
                        params: i_ft_p,
                        results: i_ft_r,
                        vardecl: ty.vardecl.clone(),
                    })),
                    self.1.clone(),
                )
            }

            PreType::Ref(cap, loc, ht) => Type(
                Box::new(PreType::Ref(
                    cap.clone(),
                    loc.clone(),
                    match ht {
                        HeapType::Variant(vec_ty) => HeapType::Variant(
                            vec_ty
                                .iter()
                                .map(|ty| ty.instantiate_ty(ty_var_map))
                                .collect(),
                        ),
                        HeapType::Struct(vec_ty) => HeapType::Struct(
                            vec_ty
                                .iter()
                                .map(|(ty, sz)| (ty.instantiate_ty(ty_var_map), sz.clone()))
                                .collect(),
                        ),
                        HeapType::Array(ty) => HeapType::Array(ty.instantiate_ty(ty_var_map)),
                        HeapType::Exists(qual, sz, ty) => HeapType::Exists(
                            qual.clone(),
                            sz.clone(),
                            ty.instantiate_ty(ty_var_map),
                        ),
                    },
                )),
                self.1.clone(),
            ),

            // Rec is a Recursive Type, compiled as inner types
            // We have an invariant that its not infinitely deep withut some level of indirection
            PreType::Rec(_, inner_ty) | PreType::ExLoc(inner_ty) => {
                inner_ty.instantiate_ty(ty_var_map)
            }

            _ => self.clone(),
        }
    }

    fn box_on_heap(
        instantiated_ty: &Type,
        fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) -> u32 {
        let instantiated_ty = instantiated_ty.get_pt();

        // Malloc size of the types
        let pretype_size = instantiated_ty.to_u32(fun_ctx);
        instrs.push(wasm::Instr::Const(wasm::Val::I32(pretype_size as i32)));
        instrs.push(mod_ctx.malloc.clone());

        // Save pointer since we have to push on the stack after all the mallocs are done
        let type_var_ptr = temp_locals.get_new_local_var(wasm::ValType::I32);
        instrs.push(temp_locals.set_local_var(type_var_ptr));

        // Set working pointer to the end of the allocation
        // We are working backwards since you will pop values off the stack in reverse
        let working_ptr = temp_locals.get_new_local_var(wasm::ValType::I32);
        let get_working_ptr = temp_locals.get_local_var(working_ptr);
        let set_working_ptr = temp_locals.set_local_var(working_ptr);
        instrs.push(temp_locals.get_local_var(type_var_ptr));
        instrs.push(wasm::Instr::Const(wasm::Val::I32(pretype_size as i32)));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
        instrs.push(set_working_ptr.clone());

        // For each wasm val type
        let wasm_types = instantiated_ty.to_wasm_types(fun_ctx);
        for wasm_ty in wasm_types.iter().rev() {
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

        type_var_ptr
    }

    fn unbox_from_heap(
        instantiated_ty: &Type,
        fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) -> Vec<u32> {
        let mut locals = vec![];

        let instantiated_type = instantiated_ty.get_pt();

        // We have to free the pointer to the heap location so, save it.
        let ptr = temp_locals.get_new_local_var(wasm::ValType::I32);
        instrs.push(temp_locals.set_local_var(ptr));

        // The pointer to the heap location is on TOS.
        // Save working pointer in a local variable
        let working_ptr = temp_locals.get_new_local_var(wasm::ValType::I32);
        instrs.push(temp_locals.get_local_var(ptr));
        instrs.push(wasm::Instr::Const(wasm::Val::I32(
            instantiated_type.to_u32(fun_ctx) as i32,
        )));
        instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Add));
        instrs.push(temp_locals.set_local_var(working_ptr));

        // Go through the wasm_types of the instantiated type and read out of the heap.
        for wasm_ty in instantiated_type.to_wasm_types(fun_ctx).iter().rev() {
            // Update pointer by size of wasm type
            instrs.push(temp_locals.get_local_var(working_ptr));
            instrs.push(wasm::Instr::Const(wasm::Val::I32(get_size(*wasm_ty))));
            instrs.push(wasm::Instr::Binary(wasm::BinaryOp::I32Sub));
            instrs.push(temp_locals.set_local_var(working_ptr));

            // Load from memory and save in local
            instrs.push(temp_locals.get_local_var(working_ptr));
            instrs.push(load(*wasm_ty));

            let local = temp_locals.get_new_local_var(*wasm_ty);
            instrs.push(temp_locals.set_local_var(local));
            locals.push(local);
        }

        instrs.push(temp_locals.get_local_var(ptr));
        instrs.push(mod_ctx.free.clone());

        temp_locals.free_local_var(ptr);
        temp_locals.free_local_var(working_ptr);

        locals
    }

    // For this function, the view is on the callee types.
    pub(crate) fn to_callee_stack(
        caller: &Type,
        callee: &Type,
        caller_fun_ctx: &FunctionContext,
        callee_fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) -> Vec<u32> {
        let mut locals = vec![];

        match (callee.get_pt(), caller.get_pt()) {
            // TODO: Instead of just boxing on the heap all the time,
            // Look up size of type variable
            // If it is of unbounded size, then only box on the heap.
            // Other pack as neccessary

            // Callee expects a variable and Caller has a variable, so leave as is.
            (PreType::Var(_), PreType::Var(_)) => {
                let local = temp_locals.get_new_local_var(wasm::ValType::I32);
                instrs.push(temp_locals.set_local_var(local));
                locals.push(local);
            }

            // Callee expects a variable and caller has a concrete type.
            // Box on the heap and pass pointer
            (PreType::Var(_), _) => locals.push(Self::box_on_heap(caller, caller_fun_ctx, mod_ctx, instrs, temp_locals)),

            // Callee expects a concrete type and caller has a variable.
            // Unbox from the heap and pass values read out.
            (_, PreType::Var(_)) => {
                trace!("In var");
                locals.append(&mut Self::unbox_from_heap(callee, callee_fun_ctx, mod_ctx, instrs, temp_locals));
            }
            // Callee expects a Concrete type and the caller is a concrete type.
            (PreType::Constant(callee_ty), PreType::Constant(caller_ty)) => {
                assert!(
                    callee_ty == caller_ty,
                    "Concrete constant types for caller and callees should have the same type.",
                );
                let local = temp_locals.get_new_local_var(callee_ty.to_wasm_valtype());
                instrs.push(temp_locals.set_local_var(local));
                locals.push(local);
            }
            (
                PreType::Rec(_, callee_inner_ty) | PreType::ExLoc(callee_inner_ty),
                PreType::Rec(_, caller_inner_ty) | PreType::ExLoc(caller_inner_ty),
            ) => {
                locals.append(&mut Self::to_callee_stack(
                    caller_inner_ty,
                    callee_inner_ty,
                    caller_fun_ctx,
                    callee_fun_ctx,
                    mod_ctx,
                    instrs,
                    temp_locals,
                ));
            }

            (PreType::Product(callee_vec_ty), PreType::Product(caller_vec_ty)) => {
                for (callee_ty, caller_ty) in
                    callee_vec_ty.iter().rev().zip(caller_vec_ty.iter().rev())
                {
                    trace!("INSTRS: "); 
                    instrs.iter().for_each(|i| trace!("  {i}"));
                    trace!("CALLEE type in Prod: {callee_ty:?}");
                    locals.append(&mut Self::to_callee_stack(
                        caller_ty,
                        callee_ty,
                        caller_fun_ctx,
                        callee_fun_ctx,
                        mod_ctx,
                        instrs,
                        temp_locals,
                    ));
                }
            }
            
            (PreType::Ptr(_) | PreType::CodeRef(_) | PreType::Ref(_, _, _),
                PreType::Ptr(_) | PreType::CodeRef(_) | PreType::Ref(_, _, _),
            ) => {
                trace!("in coderef");
                let local = temp_locals.get_new_local_var(wasm::ValType::I32);
                instrs.push(temp_locals.set_local_var(local));
                trace!("INSTRS: "); 
                instrs.iter().for_each(|i| trace!("  {i}"));
                locals.push(local);
            }
            
            (
                PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _),
                PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _),
            ) => (),

            (_, _) => panic!("Caller and callees should have the same concrete type, Caller:{caller:?}, Callee:{callee:?} found when trying to transform the stack to what the caller expects"),
            
        }

        locals
    }

    // For this function, the view is on the caller types.
    pub(crate) fn to_caller_stack(
        caller: &Type,
        callee: &Type,
        caller_fun_ctx: &FunctionContext,
        callee_fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) -> Vec<u32> {
        let mut locals = vec![];

        match (caller.get_pt(), callee.get_pt()) {
            // TODO: Instead of just boxing on the heap all the time,
            // Look up size of type variable
            // If it is of unbounded size, then only box on the heap.
            // Other pack as neccessary

            // Caller expects a variable and Callee has a variable, so leave as is.
            (PreType::Var(_), PreType::Var(_)) => {
                let local = temp_locals.get_new_local_var(wasm::ValType::I32);
                instrs.push(temp_locals.set_local_var(local));
                locals.push(local);
            }

            // Caller expects a variable and callee is a concrete type.
            // Box on the heap
            (PreType::Var(_), _) => 
                locals.push(Self::box_on_heap(callee, callee_fun_ctx, mod_ctx, instrs, temp_locals)),


            // Caller expects a concrete type and callee is a variable.
            // Unbox from the heap
            (_, PreType::Var(_)) => locals.append(&mut Self::unbox_from_heap(caller, caller_fun_ctx, mod_ctx, instrs, temp_locals)),

            // Caller expects a Concrete type and the callee is a concrete type.
            (PreType::Constant(caller_ty), PreType::Constant(callee_ty)) => {
                assert!(
                    caller_ty == callee_ty,
                    "Concrete constant types for caller and callees should have the same type.",
                );
                let local = temp_locals.get_new_local_var(caller_ty.to_wasm_valtype());
                instrs.push(temp_locals.set_local_var(local));
                locals.push(local);
            }

            (
                PreType::Rec(_, caller_inner_ty) | PreType::ExLoc(caller_inner_ty),
                PreType::Rec(_, callee_inner_ty) | PreType::ExLoc(callee_inner_ty),
            ) => {
                locals.append(&mut Self::to_caller_stack(
                    caller_inner_ty,
                    callee_inner_ty,
                    caller_fun_ctx,
                    callee_fun_ctx,
                    mod_ctx,
                    instrs,
                    temp_locals,
                ));
            }

            (PreType::Product(caller_vec_ty), PreType::Product(callee_vec_ty)) => {
                for (caller_ty, callee_ty) in
                caller_vec_ty.iter().rev().zip(callee_vec_ty.iter().rev())
                {
                    locals.append(&mut Self::to_caller_stack(
                        caller_ty,
                        callee_ty,
                        caller_fun_ctx,
                        callee_fun_ctx,
                        mod_ctx,
                        instrs,
                        temp_locals,
                    ));
                }
            }

            (
                PreType::Ptr(_) | PreType::CodeRef(_) | PreType::Ref(_, _, _),
                PreType::Ptr(_) | PreType::CodeRef(_) | PreType::Ref(_, _, _),
            ) => {
                let local = temp_locals.get_new_local_var(wasm::ValType::I32);
                instrs.push(temp_locals.set_local_var(local));
                locals.push(local);
            }

            (
                PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _),
                PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _),
            ) => (),

            (_, _) => panic!("Caller and callees should have the same concrete type, Caller:{caller:?}, Callee:{callee:?} found when trying to transform the stack to what the caller expects"),
        }

        locals
    }
}

impl FunctionType {
    pub(crate) fn to_callee_stack(
        caller_params: &[Type],
        callee_params: &[Type],
        caller_fun_ctx: &FunctionContext,
        callee_fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) {
        let mut param_local_vars_in_rev = vec![];
        trace!("INSTRS at start of callee_stack: ");
        instrs.iter().for_each(|i| trace!("  {i}"));

        // Go through rwasm function type params in reverse (we pop from stack so reverse)
        for (callee_param, caller_param) in
            callee_params.iter().rev().zip(caller_params.iter().rev())
        {
            param_local_vars_in_rev.append(&mut Type::to_callee_stack(
                caller_param,
                callee_param,
                caller_fun_ctx,
                callee_fun_ctx,
                mod_ctx,
                instrs,
                temp_locals,
            ));
        }

        // Go through all local variables saved in reverse order and push on the stack.
        // Free all local variables.
        for local in param_local_vars_in_rev.iter().rev() {
            instrs.push(temp_locals.get_local_var(*local));
            temp_locals.free_local_var(*local);
        }
    }

    pub(crate) fn to_caller_stack(
        caller_results: &[Type],
        callee_results: &[Type],
        caller_fun_ctx: &FunctionContext,
        callee_fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
        instrs: &mut Vec<wasm::Instr>,
        temp_locals: &mut TempLocals,
    ) {
        // Go through rwasm function type results in reverse (we pop from stack so reverse)
        //   For type variables,
        //     Look up the pretype of the type variable and go in reverse
        //     Do various loads and save data in a local variable(s)
        //   For everything else,
        //     Save in local variable(s)
        // Go through all local variables saved in reverse order, in reverse order and push on the stack.
        // Free all local variables.

        let mut results_local_vars_in_rev = vec![];

        for (caller_result, callee_result) in
            caller_results.iter().rev().zip(callee_results.iter().rev())
        {
            results_local_vars_in_rev.append(&mut Type::to_caller_stack(
                caller_result,
                callee_result,
                caller_fun_ctx,
                callee_fun_ctx,
                mod_ctx,
                instrs,
                temp_locals,
            ));
        }

        for local in results_local_vars_in_rev.iter().rev() {
            instrs.push(temp_locals.get_local_var(*local));
            temp_locals.free_local_var(*local);
        }
    }
}

impl PreType {
    pub(crate) fn to_wasm_types(&self, fun_ctx: &FunctionContext) -> Vec<wasm::ValType> {
        match self {
            PreType::Constant(ct) => match ct {
                ConstType::I32(_) => vec![wasm::ValType::I32],
                ConstType::I64(_) => vec![wasm::ValType::I64],
                ConstType::F32 => vec![wasm::ValType::F32],
                ConstType::F64 => vec![wasm::ValType::F64],
            },

            PreType::Var(_ty_var) => {
                // let size = fun_ctx.typevar_size[&ty_var.0].clone();
                // println!("size:{size:?}!");
                // let x = size.get_wasm_types(&fun_ctx.size_closure);
                // println!("var done!");
                // x
                // For now box all type variables on the heap
                vec![wasm::ValType::I32]
            }

            // Compile each of the components as adjancent types at the wasm level
            PreType::Product(vec_ty) => {
                let mut wasm_vec = Vec::new();
                for ty in vec_ty {
                    wasm_vec.append(&mut ty.to_wasm_types(fun_ctx));
                }
                wasm_vec
            }

            // Rec is a Recursive Type, compiled as inner types
            // We have an invariant that its not infinitely deep withut some level of indirection
            PreType::Rec(_, inner_ty) | PreType::ExLoc(inner_ty) => inner_ty.to_wasm_types(fun_ctx),

            // I32s because it references a value in the heap or table
            PreType::Ptr(_) | PreType::CodeRef(_) | PreType::Ref(_, _, _) => {
                vec![wasm::ValType::I32]
            }

            // Erased
            // Unit - Contains no information
            // Cap  - RichWasm capabilites are a type level construct and thus we do not need to be used in runtime.
            // Own  - Also a type level reasoning tool that can be erased during runtime.
            PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _) => Vec::new(),
            // Views into base numeric types
        }
    }

    pub(crate) fn to_size(&self, type_variable_sizes: &HashMap<u32, Size>) -> Size {
        match self {
            PreType::Constant(ct) => match ct {
                ConstType::I32(_) => Size::Concrete(32),
                ConstType::I64(_) => Size::Concrete(64),
                ConstType::F32 => Size::Concrete(32),
                ConstType::F64 => Size::Concrete(64),
            },

            PreType::Var(ty_var) => type_variable_sizes[&ty_var.0].clone(),

            PreType::Product(ty_vec) => ty_vec.iter().fold(Size::Concrete(0), |sum, ty| {
                Size::Plus(Box::new(sum), Box::new(ty.to_size(type_variable_sizes)))
            }),

            PreType::Rec(_, ty) | PreType::ExLoc(ty) => ty.to_size(type_variable_sizes),

            PreType::CodeRef(_) | PreType::Ptr(_) | PreType::Ref(_, _, _) => Size::Concrete(32),

            PreType::Unit | PreType::Own(_) | PreType::Cap(_, _, _) => Size::Concrete(0),
        }
    }

    pub(crate) fn to_u32(&self, fun_ctx: &FunctionContext) -> u32 {
        self.to_size(&fun_ctx.typevar_size)
            .to_u32(&fun_ctx.size_closure)
    }
}

impl BlockType {
    pub(crate) fn get_wasm_types(
        &self,
        fun_ctx: &FunctionContext,
    ) -> (Vec<wasm::ValType>, Vec<wasm::ValType>) {
        (
            self.params
                .iter()
                .flat_map(|ty| ty.to_wasm_types(fun_ctx))
                .collect(),
            self.results
                .iter()
                .flat_map(|ty| ty.to_wasm_types(fun_ctx))
                .collect(),
        )
    }
}

impl FunctionType {
    pub(crate) fn get_wasm_types(&self) -> (wasm::FunctionType, FunctionContext) {
        let mut size_bounds: HashMap<u32, (Vec<Size>, Vec<Size>)> = HashMap::new();
        let mut qual_bounds: HashMap<u32, (Vec<Qual>, Vec<Qual>)> = HashMap::new();
        let mut typevar_size: HashMap<u32, Size> = HashMap::new();

        // Populate the context with the values for various abstract variables.
        // These are size variables, type variables and qual variables.
        // Loc variables are erased.
        let (mut size_vars_count, mut type_vars_count, mut qual_vars_count) = (0, 0, 0);
        for var in self.vardecl.iter() {
            match var {
                // Upper and Lower bounds for the instruction translations
                VarDecl::Size(upper, lower) => {
                    size_bounds.insert(size_vars_count, (upper.clone(), lower.clone()));
                    size_vars_count += 1;
                }

                // Used in the TYPE translation of sizes
                VarDecl::Type(_qual, size, _heap) => {
                    typevar_size.insert(type_vars_count, size.clone());
                    type_vars_count += 1;
                }

                // Used in translation of VariantCase
                VarDecl::Qual(upper, lower) => {
                    qual_bounds.insert(qual_vars_count, (upper.clone(), lower.clone()));
                    qual_vars_count += 1;
                }

                // Erased
                VarDecl::Loc => (),
            }
        }
        let context = FunctionContext::new(typevar_size.clone(), &size_bounds, &qual_bounds);
        let params: Vec<wasm::ValType> = self
            .params
            .iter()
            .flat_map(|ty| ty.to_wasm_types(&context))
            .collect();
        let results: Vec<wasm::ValType> = self
            .results
            .iter()
            .flat_map(|ty| ty.to_wasm_types(&context))
            .collect();
        let ft = wasm::FunctionType::new(&params, &results);
        (ft, context)
    }
}

impl Size {
    pub(crate) fn is_size_abstract(&self) -> bool {
        match self {
            Size::Concrete(_) => false,
            Size::Abstract(_) => true,
            Size::Plus(s1, s2) => Self::is_size_abstract(s1) && Self::is_size_abstract(s2),
        }
    }

    pub(crate) fn to_u32(&self, size_variable_bounds: &HashMap<u32, u32>) -> u32 {
        trace!("getting u32 of size");
        match self {
            Size::Concrete(ty_size) => *ty_size,

            // Type variables with unknown upper size bounds will be
            // boxed on the heap and passed around by reference.
            // If unknown, 64
            Size::Abstract(ty) => {
                trace!("getting size of abstract size variable");
                let x = size_variable_bounds.get(&ty.0).unwrap();
                *x
            }

            Size::Plus(size1, size2) => {
                // If any component of a plus is abstract, the whole plus is abstract
                let size1 = size1;
                let size2 = size2;
                if size1.is_size_abstract() && size2.is_size_abstract() {
                    64
                } else {
                    size1.to_u32(size_variable_bounds) + size2.to_u32(size_variable_bounds)
                }
            }
        }
    }

    pub(crate) fn _get_wasm_types(&self, size_bounds: &HashMap<u32, u32>) -> Vec<wasm::ValType> {
        Size::translate_size_to_vals(self.to_u32(size_bounds))
    }
}

impl Function {
    pub(crate) fn translate(&self, mod_ctx: &ModuleContext) -> wasm::Function {
        let (type_, mut fun_ctx) = self._type.get_wasm_types();

        trace!(
            "wasm function_type: {:?}->{:?}",
            type_.inputs(),
            type_.results()
        );

        let mut locals_size: Vec<Size> = self
            ._type
            .params
            .iter()
            .map(|ty| ty.to_size(&fun_ctx.typevar_size))
            .collect();
        locals_size.append(&mut self.locals.clone());

        let mut all_wasm_locals = Vec::new();
        let mut all_local_types: HashMap<u32, Vec<wasm::ValType>> = HashMap::new();
        let mut local_map: HashMap<u32, Vec<u32>> = HashMap::new();
        let mut wasm_locals_count = 0;

        for (rwasm_local_idx, local_size) in locals_size.iter().enumerate() {
            let wasm_locals = Local::get_wasm_locals(local_size.to_u32(&fun_ctx.size_closure));

            let local_idx = rwasm_local_idx as u32;
            let wasm_locals_idx = (wasm_locals_count
                ..(wasm_locals_count + wasm_locals.len() as u32))
                .collect::<Vec<_>>();
            wasm_locals_count += wasm_locals.len() as u32;

            let wasm_types = wasm_locals
                .iter()
                .map(|l: &wasm::Local| l.type_)
                .collect::<Vec<_>>();

            all_wasm_locals.append(&mut wasm_locals.clone());

            trace!(
                "
            rwasm local: {rwasm_local_idx}
            rwasm local size: {local_size:?}
            wasm locals: {wasm_locals_idx:?}
            wasm local types: {wasm_types:?}"
            );

            local_map.insert(local_idx, wasm_locals_idx);
            all_local_types.insert(local_idx, wasm_types);
        }

        fun_ctx.wasm_local_types = all_local_types;
        fun_ctx.local_map = local_map.clone();

        let mut temp_locals = TempLocals::new(all_wasm_locals.len() as u32);

        let mut body = Vec::new();
        for instr in &self.body {
            let instrs = &mut translate_insts::translate_instr(
                instr,
                &fun_ctx,
                mod_ctx,
                &mut temp_locals,
            ); 
            body.append(instrs);
        }
        body.push(wasabi_wasm::Instr::End);

        all_wasm_locals.append(&mut temp_locals.get_wasm_locals());

        for (idx, wasm_local) in all_wasm_locals.iter().enumerate() {
            trace!("  LocalIdx:{} Type:{}", idx, wasm_local.type_);
        }

        for instr in body.iter() {
            trace!("  {instr}")
        }

        let code = wasm::Code {
            locals: all_wasm_locals,
            body,
        };

        wasm::Function::new(type_, code, self.export.clone())
    }
}

impl Local {
    pub(crate) fn get_wasm_locals(local_size: u32) -> Vec<wasm::Local> {
        // We erase Unit types.
        // So the size of locals with type Unit will be 0.
        // We do not create a wasm local for this rwasm local since it will (and should) never be set.
        if local_size == 0 {
            return vec![];
        }

        let wasm_locals_types = Size::translate_size_to_vals(local_size);
        let mut wasm_locals = Vec::new();

        for lty in wasm_locals_types {
            wasm_locals.push(wasm::Local {
                type_: lty,
                name: None,
            })
        }

        wasm_locals
    }
}

impl rwasm::Global {
    pub(crate) fn translate(
        &self,
        fun_ctx: &FunctionContext,
        mod_ctx: &ModuleContext,
    ) -> Vec<wasm::Global> {
        let mutability = match self._type.mutable {
            true => wasm::Mutability::Mut,
            false => wasm::Mutability::Const,
        };

        let init: wasm::ImportOrPresent<Vec<wasm::Instr>> = match self.init.clone() {
            ImportOrPresent::Import(s1, s2) => wasm::ImportOrPresent::Import(s1, s2),
            ImportOrPresent::Present(instrs) => wasm::ImportOrPresent::<Vec<wasm::Instr>>::Present(
                instrs
                    .iter()
                    .flat_map(|instr| {
                        translate_insts::translate_instr(
                            instr,
                            fun_ctx,
                            mod_ctx,
                            &mut TempLocals::new(0),
                        )
                    })
                    .collect(),
            ),
        };

        let global_types = self._type._type.to_wasm_types(fun_ctx);

        global_types
            .iter()
            .map(|wasm_ty| wasm::Global {
                type_: wasm::GlobalType(*wasm_ty, mutability),
                init: init.clone(),
                export: self.export.clone(),
            })
            .collect()
    }
}

impl rwasm::Table {
    pub(crate) fn translate(&self, mod_ctx: &ModuleContext, export_name: String) -> wasm::Table {
        // The functions are translated 1:1.
        let wasm_entries: Vec<wasm::Idx<wasm::Function>> = self
            .entries
            .iter()
            .map(|entry| wasm::Idx::<wasm::Function>::from(entry.0 as usize + mod_ctx.num_imports))
            .collect();

        // wasm_encoder needs the offset to end in an End instruction.
        let table_offset = vec![wasm::Instr::Const(wasm::Val::I32(0)), wasm::Instr::End];

        wasm::Table {
            limits: wasm::Limits {
                initial_size: wasm_entries.len() as u32,
                max_size: None,
            },
            import: None,
            elements: vec![wasm::Element {
                functions: wasm_entries,
                offset: table_offset,
            }],
            export: vec![export_name],
        }
    }
}

impl rwasm::Module {
    pub(crate) fn translate(&self, name: usize) -> wasm::Module {
        // We have to import an alloc function, a free function and a memory.
        let import_alloc = wasabi_wasm::Function::new_imported(
            wasabi_wasm::FunctionType::new(
                &[wasabi_wasm::ValType::I32],
                &[wasabi_wasm::ValType::I32],
            ),
            String::from("allocator"),
            String::from("walloc"),
            vec![],
        );

        let import_free = wasabi_wasm::Function::new_imported(
            wasabi_wasm::FunctionType::new(&[wasabi_wasm::ValType::I32], &[]),
            String::from("allocator"),
            String::from("wfree"),
            vec![],
        );

        let import_memory = wasabi_wasm::Memory::new_imported(
            wasabi_wasm::Limits {
                initial_size: 2,
                max_size: None,
            },
            "env".to_owned(),
            "memory".to_owned(),
        );

        let mut wasm_functions = Vec::new();
        wasm_functions.push(import_alloc);
        wasm_functions.push(import_free);

        let num_imports = wasm_functions.len();

        let fun_ctx = FunctionContext::new(HashMap::new(), &HashMap::new(), &HashMap::new());
        let mut mod_ctx = ModuleContext::new(num_imports, self.table.clone());

        let mut wasm_globals = Vec::new();
        let mut rwasm_global_types: HashMap<u32, PreType> = HashMap::new();
        let mut wasm_global_types: HashMap<u32, Vec<wasm::ValType>> = HashMap::new();
        let mut global_map: HashMap<u32, Vec<u32>> = HashMap::new();
        let mut wasm_globals_count = 0;

        for (ind, global) in self.globals.iter().enumerate() {
            let mut wasm_global = global.translate(&fun_ctx, &mod_ctx);
            let global_ind = ind as u32;
            let wasm_globals_idx =
                (wasm_globals_count..(wasm_globals_count + wasm_global.len() as u32)).collect();
            wasm_globals_count += wasm_global.len() as u32;

            wasm_globals.append(&mut wasm_global);
            rwasm_global_types.insert(global_ind, global._type._type.clone());
            wasm_global_types.insert(global_ind, wasm_global.iter().map(|g| g.type_.0).collect());
            global_map.insert(global_ind, wasm_globals_idx);
        }

        mod_ctx.rwasm_global_types = rwasm_global_types;

        let fts: HashMap<Ind<Function>, rwasm::FunctionType> = self
            .functions
            .iter()
            .enumerate()
            .map(|(ind, f)| (Ind::<Function>(ind as u32, PhantomData), f._type.clone()))
            .collect();
        mod_ctx.func_types = fts;

        for (func_idx, func) in self.functions.iter().enumerate() {
            trace!("Function{func_idx}");
            wasm_functions.push(func.translate(&mod_ctx));
        }

        wasm::Module {
            functions: wasm_functions,
            globals: wasm_globals,
            tables: vec![self.table.translate(&mod_ctx, name.to_string())],

            name: None,
            memories: vec![import_memory],
            start: None,
            custom_sections: Vec::new(),
            metadata: wasm::ModuleMetadata::default(),
        }
    }
}
