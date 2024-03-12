use crate::*;
use std::{hash, marker::PhantomData};
use wasabi_wasm as wasm;

/***************** Data Definition for Types in CapWasm *****************/

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) struct TypeVar<T>(pub(crate) u32, pub(crate) PhantomData<fn() -> T>); //Qual, Loc, Size, Type

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Cap {
    Read,
    ReadWrite,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum HeapableConst {
    Heapable,
    NotHeapable,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Val {
    I32,
    I64,
    F32,
    F64,
} // Num of NumType.t * (int64, int32) Either.t // TODO

impl Val {
    #[allow(dead_code)]
    pub(crate) fn to_valtype(&self) -> wasm::ValType {
        match *self {
            Val::I32 => wasm::ValType::I32,
            Val::I64 => wasm::ValType::I64,
            Val::F32 => wasm::ValType::F32,
            Val::F64 => wasm::ValType::F64,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn to_u32(&self) -> u32 {
        match *self {
            Val::I32 => 32,
            Val::I64 => 64,
            Val::F32 => 32,
            Val::F64 => 64,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Qual {
    Var(TypeVar<Qual>),
    Lin,
    GC,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) struct Loc {
    pub(crate) _abstract: TypeVar<Loc>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Size {
    Concrete(u32),
    Abstract(TypeVar<Size>),
    Plus(Box<Size>, Box<Size>), //adds the two sizes together
}

impl Size {
    // Known upper bound on size value, hence compile to
    // a series of adjacent I64s and I32s on the stack,
    // enough to store the size.
    pub(crate) fn translate_size_to_vals(size: u32) -> Vec<wasm::ValType> {
        let mut result_vec = Vec::new();
        if size > 32 {
            let (num_i64s, rem_size) = (size / 64, size % 64);
            let num_i32s = ((rem_size as f32) / 32_f32).ceil() as u32;
            result_vec.append(&mut vec![wasm::ValType::I64; num_i64s as usize]);
            result_vec.append(&mut vec![wasm::ValType::I32; num_i32s as usize]);
        } else {
            result_vec.append(&mut vec![wasm::ValType::I32]);
        }
        result_vec
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub(crate) enum Sign {
    S,
    U,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum ConstType {
    I32(Sign),
    I64(Sign),
    F32,
    F64,
}

impl ConstType {
    pub(crate) fn to_wasm_valtype(&self) -> wasm::ValType {
        match self {
            ConstType::I32(_) => wasm::ValType::I32,
            ConstType::I64(_) => wasm::ValType::I64,
            ConstType::F32 => wasm::ValType::F32,
            ConstType::F64 => wasm::ValType::F64,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum VarDecl {
    Loc,
    Qual(Vec<Qual>, Vec<Qual>),
    Size(Vec<Size>, Vec<Size>),
    Type(Qual, Size, HeapableConst),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct Type(pub(crate) Box<PreType>, pub(crate) Qual);

impl Type {
    pub(crate) fn get_pt(&self) -> &PreType {
        &self.0
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum PreType {
    Constant(ConstType),
    Var(TypeVar<Type>),
    Unit,
    Product(Vec<Type>),
    CodeRef(FunctionType),
    Rec(Qual, Type),
    Ptr(Loc),
    ExLoc(Type), //exported location?
    Own(Loc),
    Cap(Cap, Loc, HeapType),
    Ref(Cap, Loc, HeapType),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum HeapType {
    Variant(Vec<Type>), // One of the types
    Struct(Vec<(Type, Size)>),
    Array(Type),
    Exists(Qual, Size, Type), // Existential Types
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct BlockType {
    pub(crate) params: Vec<Type>,
    pub(crate) results: Vec<Type>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct FunctionType {
    pub(crate) params: Vec<Type>,
    pub(crate) results: Vec<Type>,
    pub(crate) vardecl: Vec<VarDecl>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct GlobalType {
    pub(crate) mutable: bool,
    pub(crate) _type: PreType,
}

/***************** Data Definitions for CapWasm Grammar *****************/

#[derive(Debug, Clone)]
pub(crate) struct Ind<T>(pub(crate) u32, pub(crate) PhantomData<fn() -> T>);

impl<T> PartialEq for Ind<T> {
    fn eq(&self, other: &Ind<T>) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Ind<T> {}

impl<T> hash::Hash for Ind<T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum ImportOrPresent {
    Import(String, String), // modules are numbered not named
    Present(Vec<Instr>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct Global {
    //id: Ind<Global>,
    pub(crate) _type: GlobalType,
    pub(crate) init: ImportOrPresent,
    pub(crate) export: Vec<String>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct Function {
    pub(crate) _type: FunctionType,
    pub(crate) locals: Vec<Size>,
    pub(crate) body: Vec<Instr>,
    pub(crate) init: ImportOrPresent,
    pub(crate) export: Vec<String>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct Local(u32);

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct LocalEffect(pub(crate) Vec<(Ind<Local>, Type)>);

// What is an Index?
// Index is used for polymorphism.
// TODO: They're used in Call instructions when calling a function that is polymorphic.
// TODO: They're also used to instantiate a CodeRef
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Index {
    Size(Size),
    Loc(Loc),
    Qual(Qual),
    PreType(PreType),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct Table {
    pub(crate) entries: Vec<Ind<Function>>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum UnaryOp {
    I32Eqz,
    I64Eqz,

    I32Clz,
    I32Ctz,
    I32Popcnt,

    I64Clz,
    I64Ctz,
    I64Popcnt,

    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,

    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,

    I32WrapI64,
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,

    I64ExtendI32S,
    I64ExtendI32U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,

    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,

    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,

    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum BinaryOp {
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,

    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,

    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,

    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,

    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,

    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,

    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,

    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum NumericInstr {
    Unary(UnaryOp),
    Binary(BinaryOp),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum LocalOp {
    Get(Qual, PreType),
    Set(Type),
    Tee(Type),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum GlobalOp {
    Get,
    Set,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum ArrayOp {
    Malloc(Qual),
    Get,
    Set,
    Free,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum StructOp {
    Malloc(Vec<Size>, Qual),
    Get(u32),
    Set(u32),
    Free,
    Swap(u32),
} //u32 being passed is field number

pub(crate) type InstrList = Vec<Instr>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Instr {
    Constant(ConstType, u32),
    Unit,

    Unreachable,
    Nop,
    Drop,

    Block(BlockType, LocalEffect, InstrList),
    Loop(BlockType, InstrList),
    IfThenElse(BlockType, LocalEffect, InstrList, InstrList),
    Select,

    Br(u32),
    BrIf(u32),
    BrTable(u32, Vec<u32>),

    Return,

    Numeric(NumericInstr),

    Local(LocalOp, u32), //TODO:Size/Type information might also be passed
    Global(GlobalOp, u32),

    CodeRef(Ind<Function>),
    Inst(Vec<Index>),
    CallIndirect(BlockType),

    Call(Ind<Function>, Vec<Index>),

    RecFold(PreType),
    RecUnfold,

    Group(u32, Qual), //u32 is group n things
    UnGroup,
    CapSplit,
    CapJoin,
    RefDemote,

    MemPack(Loc),
    MemUnpack(BlockType, LocalEffect, InstrList),

    Struct(StructOp, Vec<Type>),
    Array(ArrayOp, Type),

    VariantMalloc(u32, Vec<Type>, Qual), //int tells you access into Vec, 0 indexing  //TODO: might change, probably not
    VariantCase(Qual, Vec<Type>, BlockType, LocalEffect, Vec<InstrList>),

    ExistPack(PreType, HeapType, Qual),
    ExistUnpack(Qual, BlockType, LocalEffect, InstrList, Type),

    RefSplit,
    RefJoin,

    Qualify(Qual),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Module {
    pub(crate) functions: Vec<Function>,
    pub(crate) table: Table,
    pub(crate) globals: Vec<Global>,
}

impl Module {
    pub(crate) fn from_file(
        path: impl AsRef<std::path::Path>,
        single_module: bool,
    ) -> Result<Vec<Module>, String> {
        let modules = if single_module {
            let module = parse::single_module_from_file(path)?;
            vec![module]
        } else {
            parse::multiple_modules_from_file(path)?
        };
        Ok(modules)
    }
}
