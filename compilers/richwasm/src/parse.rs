// Parse textual representation of CapWasm
use crate::rwasm::*;

use std::{fs, marker::PhantomData};

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, multispace0, newline, u32},
    combinator::{map, value},
    error::ParseError,
    multi::many0,
    sequence::{delimited, pair, preceded, tuple},
    IResult,
};

// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
// trailing whitespace, returning the output of `inner`.
fn ws<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(
        alt((multispace0, map(newline, |_| ""))),
        inner,
        alt((multispace0, map(newline, |_| ""))),
    )
}

// A combinator that takes a parser `inner` and produces a parser that also consumes both leading "(" and
// trailing ")", returning the output of `inner`.
fn sexp<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(ws(tag("(")), inner, ws(tag(")")))
}

// A combinator that takes a parser `inner` and produces a parser that
// consumes a vector of those things and returns an Vec of that object
fn vec<'a, F, O, E: ParseError<&'a str>>(
    inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<O>, E>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, E>,
{
    sexp(many0(ws(inner)))
}

fn _bool(input: &str) -> IResult<&str, bool> {
    trace!("Parsing Bool");
    alt((value(false, ws(tag("false"))), value(true, ws(tag("true")))))(input)
}

fn cap(input: &str) -> IResult<&str, Cap> {
    trace!("Parsing Cap");
    alt((
        value(Cap::Read, ws(tag("R"))),
        value(Cap::ReadWrite, ws(tag("W"))),
    ))(input)
}

fn heapable_const(input: &str) -> IResult<&str, HeapableConst> {
    trace!("Parsing Heapable Const");
    alt((
        value(HeapableConst::Heapable, ws(tag("Heapable"))),
        value(HeapableConst::NotHeapable, ws(tag("NotHeapable"))),
    ))(input)
}

fn sign(input: &str) -> IResult<&str, Sign> {
    trace!("Parsing Sign");

    alt((value(Sign::S, ws(tag("S"))), value(Sign::U, ws(tag("U")))))(input)
}

fn qual(input: &str) -> IResult<&str, Qual> {
    trace!("Parsing Qual");

    fn qual_const(input: &str) -> IResult<&str, Qual> {
        ws(alt((
            value(Qual::Lin, tag("Lin")),
            value(Qual::GC, tag("Unr")),
        )))(input)
    }

    fn qual_v(input: &str) -> IResult<&str, Qual> {
        ws(map(u32, |digit| {
            Qual::Var(TypeVar::<Qual>(digit, PhantomData))
        }))(input)
    }

    sexp(alt((
        preceded(ws(tag("QualC")), ws(qual_const)),
        preceded(ws(tag("QualV")), ws(qual_v)),
    )))(input)
}

fn size(input: &str) -> IResult<&str, Size> {
    trace!("Parsing Size");

    fn sizec(input: &str) -> IResult<&str, Size> {
        map(ws(u32), Size::Concrete)(input)
    }

    fn sizev(input: &str) -> IResult<&str, Size> {
        map(ws(u32), |digit| {
            Size::Abstract(TypeVar::<Size>(digit, PhantomData))
        })(input)
    }

    fn sizeplus(input: &str) -> IResult<&str, Size> {
        map(tuple((ws(size), ws(size))), |(s1, s2)| {
            Size::Plus(Box::new(s1), Box::new(s2))
        })(input)
    }

    sexp(alt((
        preceded(ws(tag("SizeC")), ws(sizec)),
        preceded(ws(tag("SizeV")), ws(sizev)),
        preceded(ws(tag("SizeP")), ws(sizeplus)),
    )))(input)
}

fn loc(input: &str) -> IResult<&str, Loc> {
    trace!("Parsing Loc");

    sexp(map(preceded(ws(tag("LocV")), ws(u32)), |digit| Loc {
        _abstract: TypeVar::<Loc>(digit, PhantomData),
    }))(input)
}

fn vardecl(input: &str) -> IResult<&str, VarDecl> {
    trace!("Parsing VarDecl");

    fn loc_var_decl(input: &str) -> IResult<&str, VarDecl> {
        Ok((input, VarDecl::Loc))
    }

    fn qual_var_decl(input: &str) -> IResult<&str, VarDecl> {
        map(tuple((ws(vec(qual)), ws(vec(qual)))), |(q1, q2)| {
            VarDecl::Qual(q1, q2)
        })(input)
    }

    fn size_var_decl(input: &str) -> IResult<&str, VarDecl> {
        map(tuple((ws(vec(size)), ws(vec(size)))), |(q1, q2)| {
            VarDecl::Size(q1, q2)
        })(input)
    }

    fn type_var_decl(input: &str) -> IResult<&str, VarDecl> {
        map(
            tuple((ws(qual), ws(size), ws(heapable_const))),
            |(q, s, hc)| VarDecl::Type(q, s, hc),
        )(input)
    }

    sexp(alt((
        preceded(ws(tag("Loc")), ws(loc_var_decl)),
        preceded(ws(tag("Qual")), ws(qual_var_decl)),
        preceded(ws(tag("Size")), ws(size_var_decl)),
        preceded(ws(tag("Type")), ws(type_var_decl)),
    )))(input)
}

fn numtype(input: &str) -> IResult<&str, ConstType> {
    trace!("Parsing Numtypes");
    
    fn int_type(input: &str) -> IResult<&str, ConstType> {
        let (input, s) = ws(sign)(input)?;
        alt((
            value(ConstType::I32(s), ws(tag("I32"))),
            value(ConstType::I64(s), ws(tag("I64"))),
        ))(input)
    }

    fn float_type(input: &str) -> IResult<&str, ConstType> {
        alt((
            value(ConstType::F32, ws(tag("F32"))),
            value(ConstType::F64, ws(tag("F64"))),
        ))(input)
    }

    sexp(alt((
        preceded(ws(tag("Int")), ws(int_type)),
        preceded(ws(tag("Float")), ws(float_type)),
    )))(input)
}

fn pretype(input: &str) -> IResult<&str, PreType> {
    trace!("Parsing PreType");

    fn _num(input: &str) -> IResult<&str, PreType> {
        map(ws(numtype), PreType::Constant)(input)
    }

    fn _var(input: &str) -> IResult<&str, PreType> {
        map(ws(u32), |digit| {
            PreType::Var(TypeVar::<Type>(digit, PhantomData))
        })(input)
    }

    fn unit(input: &str) -> IResult<&str, PreType> {
        Ok((input, PreType::Unit))
    }

    fn prod(input: &str) -> IResult<&str, PreType> {
        map(ws(vec(_type)), PreType::Product)(input)
    }

    fn coderef(input: &str) -> IResult<&str, PreType> {
        map(ws(functiontype), PreType::CodeRef)(input)
    }

    fn rec(input: &str) -> IResult<&str, PreType> {
        map(tuple((ws(qual), ws(_type))), |(q, ty)| PreType::Rec(q, ty))(input)
    }

    fn ptr(input: &str) -> IResult<&str, PreType> {
        map(ws(loc), PreType::Ptr)(input)
    }

    fn exloc(input: &str) -> IResult<&str, PreType> {
        map(ws(_type), PreType::ExLoc)(input)
    }

    fn own(input: &str) -> IResult<&str, PreType> {
        map(ws(loc), PreType::Own)(input)
    }

    fn _cap(input: &str) -> IResult<&str, PreType> {
        map(tuple((ws(cap), ws(loc), ws(heaptype))), |(c, l, ht)| {
            PreType::Cap(c, l, ht)
        })(input)
    }

    fn _ref(input: &str) -> IResult<&str, PreType> {
        map(tuple((ws(cap), ws(loc), ws(heaptype))), |(c, l, ht)| {
            PreType::Ref(c, l, ht)
        })(input)
    }

    alt((
        preceded(ws(tag("Unit")), unit),
        sexp(alt((
            preceded(ws(tag("Num")), _num),
            preceded(ws(tag("Var")), _var),
            preceded(ws(tag("Prod")), prod),
            preceded(ws(tag("Coderef")), coderef),
            preceded(ws(tag("Rec")), rec),
            preceded(ws(tag("Ptr")), ptr),
            preceded(ws(tag("ExLoc")), exloc),
            preceded(ws(tag("Own")), own),
            preceded(ws(tag("Cap")), _cap),
            preceded(ws(tag("Ref")), _ref),
        ))),
    ))(input)
}

fn heaptype(input: &str) -> IResult<&str, HeapType> {
    trace!("Parsing HeapType");

    fn variant(input: &str) -> IResult<&str, HeapType> {
        map(ws(vec(_type)), HeapType::Variant)(input)
    }

    fn _struct(input: &str) -> IResult<&str, HeapType> {
        sexp(map(
            many0(sexp(map(tuple((ws(_type), ws(size))), |(ty, s)| (ty, s)))),
            HeapType::Struct,
        ))(input)
    }

    fn array(input: &str) -> IResult<&str, HeapType> {
        map(ws(_type), HeapType::Array)(input)
    }

    fn exists(input: &str) -> IResult<&str, HeapType> {
        map(tuple((ws(qual), ws(size), ws(_type))), |(q, s, ty)| {
            HeapType::Exists(q, s, ty)
        })(input)
    }

    sexp(alt((
        preceded(tag("Variant"), variant),
        preceded(tag("Struct"), _struct),
        preceded(tag("Array"), array),
        preceded(tag("Ex"), exists),
    )))(input)
}

fn blocktype(input: &str) -> IResult<&str, BlockType> {
    trace!("Parsing BlockType");

    sexp(map(
        tuple((ws(vec(_type)), ws(vec(_type)))),
        |(params, results)| BlockType { params, results },
    ))(input)
}

pub(crate) fn _type(input: &str) -> IResult<&str, Type> {
    trace!("Parsing Type input {:?}", input.get(..50));

    sexp(map(tuple((ws(pretype), ws(qual))), |(pt, q)| {
        Type(Box::new(pt), q)
    }))(input)
}

fn functiontype(input: &str) -> IResult<&str, FunctionType> {
    trace!("Parsing FunctionType");

    sexp(map(
        tuple((
            ws(vec(vardecl)),
            sexp(tuple((ws(vec(_type)), ws(vec(_type))))),
        )),
        |(vardecl, (params, results))| FunctionType {
            params,
            results,
            vardecl,
        },
    ))(input)
}

fn table(input: &str) -> IResult<&str, Table> {
    trace!("Parsing Table");

    sexp(map(many0(ws(u32)), |vec_digits| Table {
        entries: vec_digits
            .into_iter()
            .map(|d| Ind::<Function>(d, PhantomData))
            .collect(),
    }))(input)
}

fn local_effect(input: &str) -> IResult<&str, LocalEffect> {
    trace!("Parsing Local Effects");

    sexp(map(many0(sexp(tuple((ws(u32), ws(_type))))), |v| {
        LocalEffect(
            v.into_iter()
                .map(|(d, ty)| (Ind::<Local>(d, PhantomData), ty))
                .collect(),
        )
    }))(input)
}

fn index(input: &str) -> IResult<&str, Index> {
    trace!("Parsing Index");

    fn loci(input: &str) -> IResult<&str, Index> {
        map(ws(loc), Index::Loc)(input)
    }

    fn sizei(input: &str) -> IResult<&str, Index> {
        map(ws(size), Index::Size)(input)
    }

    fn quali(input: &str) -> IResult<&str, Index> {
        map(ws(qual), Index::Qual)(input)
    }

    fn pretypei(input: &str) -> IResult<&str, Index> {
        map(ws(pretype), Index::PreType)(input)
    }

    sexp(alt((
        preceded(ws(tag("LocI")), loci),
        preceded(ws(tag("SizeI")), sizei),
        preceded(ws(tag("QualI")), quali),
        preceded(ws(tag("PretypeI")), pretypei),
    )))(input)
}

fn val(input: &str) -> IResult<&str, Val> {
    trace!("Parsing Val");
    alt((
        value(Val::I32, ws(tag("I32"))),
        value(Val::I64, ws(tag("I64"))),
        value(Val::F32, ws(tag("F32"))),
        value(Val::F64, ws(tag("F64"))),
    ))(input)
}

fn numeric(input: &str) -> IResult<&str, NumericInstr> {
    trace!("Parsing Numeric");
    fn iu(input: &str) -> IResult<&str, NumericInstr> {
        fn iunop_i32(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing IUnOp32");
            alt((
                value(UnaryOp::I32Clz, ws(tag("Iclz"))),
                value(UnaryOp::I32Ctz, ws(tag("Ictz"))),
                value(UnaryOp::I32Popcnt, tag("Ipopcnt")),
            ))(input)
        }

        fn iunop_i64(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing IUnOp64");
            alt((
                value(UnaryOp::I64Clz, tag("Iclz")),
                value(UnaryOp::I64Ctz, tag("Ictz")),
                value(UnaryOp::I64Popcnt, tag("Ipopcnt")),
            ))(input)
        }

        let (input, ty) = ws(val)(input)?;
        let (input, iunop) = match ty {
            Val::I32 => iunop_i32,
            Val::I64 => iunop_i64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Unary(iunop)))
    }

    fn ib(input: &str) -> IResult<&str, NumericInstr> {
        fn ibinop_i32(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing Ib32");
            alt((
                value(BinaryOp::I32Add, ws(tag("Iadd"))),
                value(BinaryOp::I32Sub, ws(tag("Isub"))),
                value(BinaryOp::I32Mul, ws(tag("Imul"))),
                value(BinaryOp::I32DivS, sexp(tuple((ws(tag("Idiv")), ws(tag("S")))))),
                value(BinaryOp::I32DivU, sexp(tuple((ws(tag("Idiv")), ws(tag("U")))))),
                value(BinaryOp::I32RemS, sexp(tuple((ws(tag("Irem")), ws(tag("S")))))),
                value(BinaryOp::I32RemU, sexp(tuple((ws(tag("Irem")), ws(tag("U")))))),
                value(BinaryOp::I32And, ws(tag("Iand"))),
                value(BinaryOp::I32Or, ws(tag("Ior"))),
                value(BinaryOp::I32Xor, ws(tag("Ixor"))),
                value(BinaryOp::I32Shl, ws(tag("Ishl"))),
                value(BinaryOp::I32ShrS, sexp(tuple((ws(tag("Ishr")), ws(tag("S")))))),
                value(BinaryOp::I32ShrU, sexp(tuple((ws(tag("Ishr")), ws(tag("U")))))),
                value(BinaryOp::I32Rotl, ws(tag("Irotl"))),
                value(BinaryOp::I32Rotr, ws(tag("Irotr"))),
            ))(input)
        }

        fn ibinop_i64(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing Ib64");
            alt((
                value(BinaryOp::I64Add, ws(tag("Iadd"))),
                value(BinaryOp::I64Sub, ws(tag("Isub"))),
                value(BinaryOp::I64Mul, ws(tag("Imul"))),
                value(BinaryOp::I64DivS, sexp(tuple((ws(tag("Idiv")), ws(tag("S")))))),
                value(BinaryOp::I64DivU, sexp(tuple((ws(tag("Idiv")), ws(tag("U")))))),
                value(BinaryOp::I64RemS, sexp(tuple((ws(tag("Irem")), ws(tag("S")))))),
                value(BinaryOp::I64RemU, sexp(tuple((ws(tag("Irem")), ws(tag("U")))))),
                value(BinaryOp::I64And, ws(tag("Iand"))),
                value(BinaryOp::I64Or, ws(tag("Ior"))),
                value(BinaryOp::I64Xor, ws(tag("Ixor"))),
                value(BinaryOp::I64Shl, ws(tag("Ishl"))),
                value(BinaryOp::I64ShrS, sexp(tuple((ws(tag("Ishr")), ws(tag("S")))))),
                value(BinaryOp::I64ShrU, sexp(tuple((ws(tag("Ishr")), ws(tag("U")))))),
                value(BinaryOp::I64Rotl, ws(tag("Irotl"))),
                value(BinaryOp::I64Rotr, ws(tag("Irotr"))),
            ))(input)
        }

        let (input, ty) = val(input)?;
        let (input, ibinop) = match ty {
            Val::I32 => ibinop_i32,
            Val::I64 => ibinop_i64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Binary(ibinop)))
    }

    fn fu(input: &str) -> IResult<&str, NumericInstr> {
        fn funop_f32(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing FUnOp32");
            alt((
                value(UnaryOp::F32Abs, tag("Iabs")),
                value(UnaryOp::F32Neg, tag("Ineq")),
                value(UnaryOp::F32Sqrt, tag("Isqrt")),
                value(UnaryOp::F32Ceil, tag("Iceil")),
                value(UnaryOp::F32Floor, tag("Ifloor")),
                value(UnaryOp::F32Trunc, tag("Itrunc")),
                value(UnaryOp::F32Nearest, tag("Inearest")),
            ))(input)
        }

        fn funop_f64(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing FUnOp64");
            alt((
                value(UnaryOp::F64Abs, tag("Iabs")),
                value(UnaryOp::F64Neg, tag("Ineq")),
                value(UnaryOp::F64Sqrt, tag("Isqrt")),
                value(UnaryOp::F64Ceil, tag("Iceil")),
                value(UnaryOp::F64Floor, tag("Ifloor")),
                value(UnaryOp::F64Trunc, tag("Itrunc")),
                value(UnaryOp::F64Nearest, tag("Inearest")),
            ))(input)
        }

        let (input, ty) = val(input)?;
        let (input, funop) = match ty {
            Val::F32 => funop_f32,
            Val::F64 => funop_f64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Unary(funop)))
    }

    fn fb(input: &str) -> IResult<&str, NumericInstr> {
        fn fbinop_f32(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing FBinOp32");
            alt((
                value(BinaryOp::F32Add, ws(tag("Iaddf"))),
                value(BinaryOp::F32Sub, ws(tag("Isubf"))),
                value(BinaryOp::F32Mul, ws(tag("Imulf"))),
                value(BinaryOp::F32Div, ws(tag("Idivf"))),
                value(BinaryOp::F32Min, ws(tag("Imin"))),
                value(BinaryOp::F32Max, ws(tag("Imax"))),
                value(BinaryOp::F32Copysign, ws(tag("Icopysign"))),
            ))(input)
        }

        fn fbinop_f64(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing FBinOp64");
            alt((
                value(BinaryOp::F64Add, ws(tag("Iaddf"))),
                value(BinaryOp::F64Sub, ws(tag("Isubf"))),
                value(BinaryOp::F64Mul, ws(tag("Imulf"))),
                value(BinaryOp::F64Div, ws(tag("Idivf"))),
                value(BinaryOp::F64Min, ws(tag("Imin"))),
                value(BinaryOp::F64Max, ws(tag("Imax"))),
                value(BinaryOp::F64Copysign, ws(tag("Icopysign"))),
            ))(input)
        }

        let (input, ty) = val(input)?;
        let (input, fbinop) = match ty {
            Val::F32 => fbinop_f32,
            Val::F64 => fbinop_f64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Binary(fbinop)))
    }

    fn it(input: &str) -> IResult<&str, NumericInstr> {
        fn itestop_i32(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing ITestOp32");
            value(UnaryOp::I32Eqz, tag("Ieqz"))(input)
        }

        fn itestop_i64(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing ITestOp64");
            value(UnaryOp::I64Eqz, tag("Ieqz"))(input)
        }

        let (input, ty) = val(input)?;
        let (input, itestop) = match ty {
            Val::I32 => itestop_i32,
            Val::I64 => itestop_i64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Unary(itestop)))
    }

    fn ir(input: &str) -> IResult<&str, NumericInstr> {
        fn irelop_i32(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing IRelOp32");
            alt((
                value(BinaryOp::I32Eq, ws(tag("Ieq"))),
                value(BinaryOp::I32Ne, ws(tag("Ine"))),
                value(BinaryOp::I32LtS, sexp(pair(ws(tag("Ilt")), ws(tag("S"))))),
                value(BinaryOp::I32GtS, sexp(pair(ws(tag("Igt")), ws(tag("S"))))),
                value(BinaryOp::I32LeS, sexp(pair(ws(tag("Ile")), ws(tag("S"))))),
                value(BinaryOp::I32GeS, sexp(pair(ws(tag("Ige")), ws(tag("S"))))),
                value(BinaryOp::I32LtU, sexp(pair(ws(tag("Ilt")), ws(tag("U"))))),
                value(BinaryOp::I32GtU, sexp(pair(ws(tag("Igt")), ws(tag("U"))))),
                value(BinaryOp::I32LeU, sexp(pair(ws(tag("Ile")), ws(tag("U"))))),
                value(BinaryOp::I32GeU, sexp(pair(ws(tag("Ige")), ws(tag("U"))))),
            ))(input)
        }

        fn irelop_i64(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing IRelOp64");
            alt((
                value(BinaryOp::I64Eq, ws(tag("Ieq"))),
                value(BinaryOp::I64Ne, ws(tag("Ine"))),
                value(BinaryOp::I64LtS, sexp(pair(ws(tag("Ilt")), ws(tag("S"))))),
                value(BinaryOp::I64GtS, sexp(pair(ws(tag("Igt")), ws(tag("S"))))),
                value(BinaryOp::I64LeS, sexp(pair(ws(tag("Ile")), ws(tag("S"))))),
                value(BinaryOp::I64GeS, sexp(pair(ws(tag("Ige")), ws(tag("S"))))),
                value(BinaryOp::I64LtU, sexp(pair(ws(tag("Ilt")), ws(tag("U"))))),
                value(BinaryOp::I64GtU, sexp(pair(ws(tag("Igt")), ws(tag("U"))))),
                value(BinaryOp::I64LeU, sexp(pair(ws(tag("Ile")), ws(tag("U"))))),
                value(BinaryOp::I64GeU, sexp(pair(ws(tag("Ige")), ws(tag("U"))))),
            ))(input)
        }

        let (input, ty) = val(input)?;
        let (input, irelop) = match ty {
            Val::I32 => irelop_i32,
            Val::I64 => irelop_i64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Binary(irelop)))
    }

    fn fr(input: &str) -> IResult<&str, NumericInstr> {
        fn frelop_f32(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing FRelOp32");
            alt((
                value(BinaryOp::F32Eq, ws(tag("Ieqf"))),
                value(BinaryOp::F32Ne, ws(tag("Inef"))),
                value(BinaryOp::F32Lt, ws(tag("Iltf"))),
                value(BinaryOp::F32Gt, ws(tag("Igtf"))),
                value(BinaryOp::F32Le, ws(tag("Ilef"))),
                value(BinaryOp::F32Ge, ws(tag("Igef"))),
            ))(input)
        }

        fn frelop_f64(input: &str) -> IResult<&str, BinaryOp> {
            trace!("Parsing FRelOp64");
            alt((
                value(BinaryOp::F64Eq, ws(tag("Ieqf"))),
                value(BinaryOp::F64Ne, ws(tag("Inef"))),
                value(BinaryOp::F64Lt, ws(tag("Iltf"))),
                value(BinaryOp::F64Gt, ws(tag("Igtf"))),
                value(BinaryOp::F64Le, ws(tag("Ilef"))),
                value(BinaryOp::F64Ge, ws(tag("Igef"))),
            ))(input)
        }

        let (input, ty) = val(input)?;
        let (input, frelop) = match ty {
            Val::F32 => frelop_f32,
            Val::F64 => frelop_f64,
            _ => todo!(),
        }(input)?;
        Ok((input, NumericInstr::Binary(frelop)))
    }

    fn cvti(input: &str) -> IResult<&str, NumericInstr> {
        trace!("Parsing CvtI");

        // fn i32_convert_i32(input: &str) -> IResult<&str, ()> {
        //    trace!("Parsing CvtI IConvery");
        //    // CvtI I32(IConvert I32 U)
        //    let (input, _) = tuple((
        //        ws(tag("I32")), 
        //        sexp(tuple((
        //            ws(),
        //            ws(tag("I32")), 
        //            ws(sign)))
        //        )
        //    ))(input)?;
        //    
        //    Ok((input, ()))
        //}

        fn i32_wrap_i64(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing I32Wrap64");
            let (input, ty) = val(input)?;
            match ty {
                Val::I64 => Ok((input, UnaryOp::I32WrapI64)),
                _ => todo!(),
            }
        }

        fn i64_extend_i32(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing I64Extend32");
            let (input, ty) = val(input)?;
            let (input, sign) = sign(input)?;
            match ty {
                Val::I32 => match sign {
                    Sign::S => Ok((input, UnaryOp::I64ExtendI32S)),
                    Sign::U => Ok((input, UnaryOp::I64ExtendI32U)),
                },
                _ => todo!(),
            }
        }

        fn reinterpret_i2f(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing ReInterpretI2F");
            let (input, ty) = ws(val)(input)?;
            Ok((
                input,
                match ty {
                    Val::F32 => UnaryOp::I32ReinterpretF32,
                    Val::F64 => UnaryOp::I64ReinterpretF64,
                    _ => todo!(),
                },
            ))
        }

        fn i32_trunc_f(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing I32TruncF");
            let (input, ty) = ws(val)(input)?;
            let (input, sign) = ws(sign)(input)?;
            Ok((
                input,
                match ty {
                    Val::F32 => match sign {
                        Sign::S => UnaryOp::I32TruncF32S,
                        Sign::U => UnaryOp::I32TruncF32U,
                    },
                    Val::F64 => match sign {
                        Sign::S => UnaryOp::I32TruncF64S,
                        Sign::U => UnaryOp::I32TruncF64U,
                    },
                    _ => todo!(),
                },
            ))
        }

        fn i64_trunc_f(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing I64TruncF");
            let (input, ty) = ws(val)(input)?;
            let (input, sign) = ws(sign)(input)?;
            Ok((
                input,
                match ty {
                    Val::F32 => match sign {
                        Sign::S => UnaryOp::I64TruncF32S,
                        Sign::U => UnaryOp::I64TruncF32U,
                    },
                    Val::F64 => match sign {
                        Sign::S => UnaryOp::I64TruncF64S,
                        Sign::U => UnaryOp::I64TruncF64U,
                    },
                    _ => todo!(),
                },
            ))
        }

        let (input, ty) = val(input)?;
        let (input, cvti) = match ty {
            Val::I32 => alt((
                preceded(ws(tag("IWrap")), i32_wrap_i64),
                preceded(ws(tag("IReinterpret")), reinterpret_i2f),
                preceded(ws(tag("ITrunc")), i32_trunc_f),
            ))(input)?,

            Val::I64 => alt((
                preceded(ws(tag("IExtend")), i64_extend_i32),
                preceded(ws(tag("IReinterpret")), reinterpret_i2f),
                preceded(ws(tag("ITrunc")), i64_trunc_f),
            ))(input)?,

            _ => todo!(),
        };
        Ok((input, NumericInstr::Unary(cvti)))
    }

    fn cvtf(input: &str) -> IResult<&str, NumericInstr> {
        trace!("Parsing Cvtf");

        fn f32_convert_i(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing F32ConvertI");
            let (input, ty) = ws(val)(input)?;
            let (input, sign) = ws(sign)(input)?;

            Ok((
                input,
                match ty {
                    Val::I32 => match sign {
                        Sign::S => UnaryOp::F32ConvertI32S,
                        Sign::U => UnaryOp::F32ConvertI32U,
                    },
                    Val::I64 => match sign {
                        Sign::S => UnaryOp::F32ConvertI64S,
                        Sign::U => UnaryOp::F32ConvertI64U,
                    },
                    _ => todo!(),
                },
            ))
        }

        fn f64_convert_i(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing F64ConvertI");
            let (input, ty) = ws(val)(input)?;
            let (input, sign) = ws(sign)(input)?;

            Ok((
                input,
                match ty {
                    Val::I32 => match sign {
                        Sign::S => UnaryOp::F64ConvertI32S,
                        Sign::U => UnaryOp::F64ConvertI32U,
                    },
                    Val::I64 => match sign {
                        Sign::S => UnaryOp::F64ConvertI64S,
                        Sign::U => UnaryOp::F64ConvertI64U,
                    },
                    _ => todo!(),
                },
            ))
        }

        fn reinterpret_f2i(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing ReInterpretF2I");
            let (input, ty) = ws(val)(input)?;
            Ok((
                input,
                match ty {
                    Val::I32 => UnaryOp::F32ReinterpretI32,
                    Val::I64 => UnaryOp::F64ReinterpretI64,
                    _ => todo!(),
                },
            ))
        }

        fn f32_demote_f64(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing F32DemoteF64");
            let (input, ty) = ws(val)(input)?;
            match ty {
                Val::F64 => Ok((input, UnaryOp::F32DemoteF64)),
                _ => todo!(),
            }
        }

        fn f64_promote_f32(input: &str) -> IResult<&str, UnaryOp> {
            trace!("Parsing F64PromoteF32");
            let (input, ty) = ws(val)(input)?;
            match ty {
                Val::F32 => Ok((input, UnaryOp::F64PromoteF32)),
                _ => todo!(),
            }
        }

        let (input, ty) = val(input)?;
        let (input, cvtf) = match ty {
            Val::F32 => alt((
                sexp(preceded(ws(tag("IConvert")), f32_convert_i)),
                sexp(preceded(ws(tag("IReinterpret")), reinterpret_f2i)),
                sexp(preceded(ws(tag("IDemote")), f32_demote_f64)),
            ))(input)?,

            Val::F64 => alt((
                preceded(ws(tag("IConvert")), f64_convert_i),
                preceded(ws(tag("IReinterpret")), reinterpret_f2i),
                preceded(ws(tag("IPromote")), f64_promote_f32),
            ))(input)?,
            _ => todo!(),
        };
        Ok((input, NumericInstr::Unary(cvtf)))
    }

    sexp(alt((
        preceded(tag("Iu"), iu),
        preceded(tag("Ib"), ib),
        preceded(tag("Fu"), fu),
        preceded(tag("Fb"), fb),
        preceded(tag("It"), it),
        preceded(tag("Ir"), ir),
        preceded(tag("Fr"), fr),
        preceded(tag("CvtI"), cvti),
        preceded(tag("CvtF"), cvtf),
    )))(input)
}

fn export(input: &str) -> IResult<&str, String> {
    trace!("Parsing Export");
    let (input, export_str) = ws(identifier)(input)?;
    Ok((input, export_str.to_owned()))
}

pub fn identifier(input: &str) -> IResult<&str, &str> {
    trace!("Parsing Identifier");
    nom::Parser::parse(&mut nom::combinator::recognize(
      pair(
        alt((nom::character::complete::alpha1, tag("_"))),
        nom::multi::many0_count(alt((alphanumeric1, tag("_"))))
      )
    ), input)
}

fn import(input: &str) -> IResult<&str, (String, String)> {
    trace!("Parsing Import");

    let (input, _) = ws(tag("("))(input)?;
    let (input, _) = ws(tag("Import"))(input)?;
    let (input, import_module) = ws(identifier)(input)?;
    let (input, import_fn) = ws(identifier)(input)?;
    let (input, _) = ws(tag(")"))(input)?;
    
    Ok((input, (import_module.to_owned(), import_fn.to_owned())))
}

fn instr(input: &str) -> IResult<&str, Instr> {
    trace!("Parsing Instruction");
    fn num(input: &str) -> IResult<&str, Instr> {
        // Num of NumType.t * (int64, int32) Either.t
        // FIXME: "First" and "Second" mean either u32 or u64 - maybe reprent accordingly
        map(
            tuple((
                ws(numtype),
                sexp(preceded(ws(alt((tag("First"), tag("Second")))), ws(u32))),
            )),
            |(ty, digit)| Instr::Constant(ty, digit),
        )(input)
    }

    fn unit(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::Unit))
    }

    fn value(input: &str) -> IResult<&str, Instr> {
        alt((
            sexp(preceded(ws(tag("Num")), ws(num))),
            preceded(ws(tag("Unit")), ws(unit)),
        ))(input)
    }

    fn ne(input: &str) -> IResult<&str, Instr> {
        map(ws(numeric), Instr::Numeric)(input)
    }

    fn unreachable(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::Unreachable))
    }
    fn nop(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::Nop))
    }
    fn drop(input: &str) -> IResult<&str, Instr> {
        trace!("Parsing Drop"); 
        // (IDrop (Ptr (LocV 0)))
        let (input, pt) = ws(pretype)(input)?;
        Ok((input, Instr::Drop(pt)))
    }
    fn select(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::Select))
    }

    fn block(input: &str) -> IResult<&str, Instr> {
        ws(map(
            tuple((ws(blocktype), ws(local_effect), ws(vec(instr)))),
            |(ty, le, b)| Instr::Block(ty, le, b),
        ))(input)
    }

    fn _loop(input: &str) -> IResult<&str, Instr> {
        ws(map(tuple((ws(blocktype), ws(vec(instr)))), |(ty, b)| {
            Instr::Loop(ty, b)
        }))(input)
    }

    fn iite(input: &str) -> IResult<&str, Instr> {
        ws(map(
            tuple((
                ws(blocktype),
                ws(local_effect),
                ws(vec(instr)),
                ws(vec(instr)),
            )),
            |(ty, le, if_b, else_b)| Instr::IfThenElse(ty, le, if_b, else_b),
        ))(input)
    }

    fn br(input: &str) -> IResult<&str, Instr> {
        ws(map(u32, Instr::Br))(input)
    }

    fn br_if(input: &str) -> IResult<&str, Instr> {
        ws(map(u32, Instr::BrIf))(input)
    }

    fn br_table(input: &str) -> IResult<&str, Instr> {
        map(tuple((sexp(many0(ws(u32))), ws(u32))), |(v, d)| {
            Instr::BrTable(d, v)
        })(input)
    }

    fn ret(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::Return))
    }

    fn tee_local(input: &str) -> IResult<&str, Instr> {
        // ITee_local of int * Type.t
        map(tuple((ws(u32), ws(_type))), |(digit, ty)| {
            Instr::Local(LocalOp::Tee(ty), digit)
        })(input)
    }

    fn get_local(input: &str) -> IResult<&str, Instr> {
        // IGet_local of int * Qual.t * Type.t
        // (IGet_local 1 (QualV 0) ((Var 0) (QualV 0)))
        map(
            tuple((ws(u32), ws(qual), ws(pretype))),
            |(digit, qual, ty)| Instr::Local(LocalOp::Get(qual, ty), digit),
        )(input)
    }

    fn set_local(input: &str) -> IResult<&str, Instr> {
        // ISet_local of int * Type.t
        map(tuple((ws(u32), ws(_type))), |(digit, ty)| {
            Instr::Local(LocalOp::Set(ty), digit)
        })(input)
    }

    fn get_global(input: &str) -> IResult<&str, Instr> {
        // IGet_global of int
        map(ws(u32), |digit| Instr::Global(GlobalOp::Get, digit))(input)
    }

    fn set_global(input: &str) -> IResult<&str, Instr> {
        // ISet_global of int
        map(ws(u32), |digit| Instr::Global(GlobalOp::Set, digit))(input)
    }

    fn coderefi(input: &str) -> IResult<&str, Instr> {
        // ICoderefI of int
        map(ws(u32), |digit| {
            Instr::CodeRef(Ind::<Function>(digit, PhantomData))
        })(input)
    }

    fn inst(input: &str) -> IResult<&str, Instr> {
        // IInst of Index.t list
        map(ws(vec(index)), Instr::Inst)(input)
    }

    fn call_indirect(input: &str) -> IResult<&str, Instr> {
        // ICall_indirect of Type.ft
        map(ws(blocktype), Instr::CallIndirect)(input)
    }

    fn call(input: &str) -> IResult<&str, Instr> {
        // ICall of int * Index.t list
        map(tuple((ws(u32), vec(index))), |(digit, inst)| {
            Instr::Call(Ind::<Function>(digit, PhantomData), inst)
        })(input)
    }

    fn rec_fold(input: &str) -> IResult<&str, Instr> {
        // IRecFold of Type.pt
        map(ws(pretype), Instr::RecFold)(input)
    }

    fn rec_unfold(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::RecUnfold))
    }

    fn group(input: &str) -> IResult<&str, Instr> {
        // IGroup of int * Qual.t
        map(tuple((ws(u32), ws(qual))), |(digit, qual)| {
            Instr::Group(digit, qual)
        })(input)
    }

    fn ungroup(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::UnGroup))
    }

    fn cap_split(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::CapSplit))
    }

    fn cap_join(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::CapJoin))
    }

    fn ref_demote(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::RefDemote))
    }

    fn mempack(input: &str) -> IResult<&str, Instr> {
        // IMemPack of Loc.t
        map(ws(loc), Instr::MemPack)(input)
    }

    fn memunpack(input: &str) -> IResult<&str, Instr> {
        // IMemUnpack of Type.at * LocalEffect.t * t list * Type
        map(
            tuple((ws(blocktype), ws(local_effect), ws(vec(instr)), ws(_type))),
            |(bt, le, instr, ty)| Instr::MemUnpack(bt, le, instr, ty),
        )(input)
    }

    fn istructmalloc(input: &str) -> IResult<&str, Instr> {
        // IStructMalloc of Size.t list * Qual.t * Type.t list
        map(
            tuple((ws(vec(size)), ws(qual), ws(vec(_type)))),
            |(v1, q, v2)| Instr::Struct(StructOp::Malloc(v1, q), v2),
        )(input)
    }

    fn istructfree(input: &str) -> IResult<&str, Instr> {
        // IStructFree of Type.t list
        map(ws(vec(_type)), |v| Instr::Struct(StructOp::Free, v))(input)
    }

    fn istructget(input: &str) -> IResult<&str, Instr> {
        // IStructGet of int * Type.t list
        map(tuple((ws(u32), ws(vec(_type)))), |(digit, v)| {
            Instr::Struct(StructOp::Get(digit), v)
        })(input)
    }

    fn istructset(input: &str) -> IResult<&str, Instr> {
        // IStructSet of int * Type.t list * PreType
        map(tuple((ws(u32), ws(vec(_type)), ws(pretype))), |(digit, v, pt)| {
            Instr::Struct(StructOp::Set(digit, pt), v)
        })(input)
    }

    fn istructswap(input: &str) -> IResult<&str, Instr> {
        // IStructSwap of int * Type.t list
        map(tuple((ws(u32), ws(vec(_type)), ws(pretype))), |(digit, v, pt)| {
            Instr::Struct(StructOp::Swap(digit, pt), v)
        })(input)
    }

    fn ivariantmalloc(input: &str) -> IResult<&str, Instr> {
        // IVariantMalloc of int * Type.t list * Qual.t
        map(
            tuple((ws(u32), ws(vec(_type)), ws(qual))),
            |(digit, ty, qual)| Instr::VariantMalloc(digit, ty, qual),
        )(input)
    }

    fn ivariantcase(input: &str) -> IResult<&str, Instr> {
        // IVariantCase of Qual.t * Type.at * LocalEffect.t * t list list
        map(
            tuple((
                ws(qual),
                vec(ws(_type)),
                ws(blocktype),
                ws(local_effect),
                ws(vec(vec(instr))),
            )),
            |(qual, ty, bt, le, instrs)| Instr::VariantCase(qual, ty, bt, le, instrs),
        )(input)
    }

    fn iarraymalloc(input: &str) -> IResult<&str, Instr> {
        // IArrayMalloc of Qual.t * Type.t
        map(tuple((ws(qual), ws(_type))), |(qual, t)| {
            Instr::Array(ArrayOp::Malloc(qual), t)
        })(input)
    }

    fn iarrayget(input: &str) -> IResult<&str, Instr> {
        // IArrayGet of Type.t
        map(ws(_type), |t| Instr::Array(ArrayOp::Get, t))(input)
    }

    fn iarrayset(input: &str) -> IResult<&str, Instr> {
        // IArraySet of Type.t
        map(ws(_type), |t| Instr::Array(ArrayOp::Set, t))(input)
    }

    fn iarrayfree(input: &str) -> IResult<&str, Instr> {
        // IArrayFree of Type.t
        map(ws(_type), |t| Instr::Array(ArrayOp::Free, t))(input)
    }

    fn iexistpack(input: &str) -> IResult<&str, Instr> {
        // IExistPack of Type.pt * Type.ht * Qual.t
        map(
            tuple((ws(pretype), ws(heaptype), ws(qual))),
            |(pt, ht, qual)| Instr::ExistPack(pt, ht, qual),
        )(input)
    }

    fn iexistunpack(input: &str) -> IResult<&str, Instr> {
        // IExistUnpack of Qual.t * Type.at * LocalEffect.t * t list
        map(
            tuple((
                ws(qual),
                ws(blocktype),
                ws(local_effect),
                ws(vec(instr)),
                ws(_type),
            )),
            |(qual, bt, le, i, ty)| Instr::ExistUnpack(qual, bt, le, i, ty),
        )(input)
    }

    fn irefsplit(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::RefSplit))
    }
    fn irefjoin(input: &str) -> IResult<&str, Instr> {
        Ok((input, Instr::RefJoin))
    }

    fn iqualify(input: &str) -> IResult<&str, Instr> {
        map(ws(qual), Instr::Qualify)(input)
    }


    fn i32_convert_i32(input: &str) -> IResult<&str, Instr> {
        trace!("Parsing CvtI IConvert");
        //(INe(CvtI I32(IConvert I32 U)))
        let (input, _) = sexp(tuple((
            ws(tag("INe")), 
            sexp(tuple((
                ws(tag("CvtI")), 
                ws(val), 
                sexp(tuple((
                    ws(tag("IConvert")),
                    ws(tag("I32")), 
                    ws(sign)    
                )))
            )))
        )))(input)?;
                
        Ok((input, Instr::Nop))
    }

    alt((
        i32_convert_i32, 
        alt((
            // Do not take any arguments so are not in sepx form
            preceded(ws(tag("IUnreachable")), unreachable),
            preceded(ws(tag("INop")), nop),
            preceded(ws(tag("ISelect")), select),
            preceded(ws(tag("IRet")), ret),
            preceded(ws(tag("IRecUnfold")), rec_unfold),
            preceded(ws(tag("IUngroup")), ungroup),
            preceded(ws(tag("ICapSplit")), cap_split),
            preceded(ws(tag("ICapJoin")), cap_join),
            preceded(ws(tag("IRefDemote")), ref_demote),
            preceded(ws(tag("IRefSplit")), irefsplit),
            preceded(ws(tag("IRefJoin")), irefjoin),
        )),
        sexp(alt((
            alt((
                preceded(ws(tag("IDrop")), drop),
                preceded(ws(tag("IVal")), value),
                preceded(ws(tag("INe")), ne),
            )),
            alt((
                preceded(ws(tag("IBlock")), block),
                preceded(ws(tag("ILoop")), _loop),
                preceded(ws(tag("IITE")), iite),
                preceded(ws(tag("IBr")), br),
                preceded(ws(tag("IBr_if")), br_if),
                preceded(ws(tag("IBr_table")), br_table),
            )),
            alt((
                preceded(ws(tag("ITee_local")), tee_local),
                preceded(ws(tag("IGet_local")), get_local),
                preceded(ws(tag("ISet_local")), set_local),
                preceded(ws(tag("IGet_global")), get_global),
                preceded(ws(tag("ISet_global")), set_global),
            )),
            alt((
                preceded(ws(tag("ICoderefI")), coderefi),
                preceded(ws(tag("IInst")), inst),
                preceded(ws(tag("ICall_indirect")), call_indirect),
                preceded(ws(tag("ICall")), call),
                preceded(ws(tag("IRecFold")), rec_fold),
                preceded(ws(tag("IGroup")), group),
                preceded(ws(tag("IMemPack")), mempack),
                preceded(ws(tag("IMemUnpack")), memunpack),
            )),
            alt((
                preceded(ws(tag("IStructMalloc")), istructmalloc),
                preceded(ws(tag("IStructFree")), istructfree),
                preceded(ws(tag("IStructGet")), istructget),
                preceded(ws(tag("IStructSet")), istructset),
                preceded(ws(tag("IStructSwap")), istructswap),
            )),
            alt((
                preceded(ws(tag("IVariantMalloc")), ivariantmalloc),
                preceded(ws(tag("IVariantCase")), ivariantcase),
            )),
            alt((
                preceded(ws(tag("IArrayMalloc")), iarraymalloc),
                preceded(ws(tag("IArrayGet")), iarrayget),
                preceded(ws(tag("IArraySet")), iarrayset),
                preceded(ws(tag("IArrayFree")), iarrayfree),
            )),
            alt((
                preceded(ws(tag("IExistPack")), iexistpack),
                preceded(ws(tag("IExistUnpack")), iexistunpack),
                preceded(ws(tag("IQualify")), iqualify),
            )),
        ))),
    ))(input)
}

fn function(input: &str) -> IResult<&str, Function> {
    trace!("Parsing Function");
    fn function_present(input: &str) -> IResult<&str, Function> {
        preceded(
            ws(tag("Fun")),
            map(
                tuple((
                    ws(vec(export)),
                    ws(functiontype),
                    ws(vec(size)),
                    ws(vec(instr)),
                )),
                |(export, _type, locals, body)| Function {
                    _type,
                    locals,
                    body,
                    init: ImportOrPresent::Present(Vec::new()),
                    export,
                },
            ),
        )(input)
    }

    fn function_import(input: &str) -> IResult<&str, Function> {
        preceded(
            ws(tag("FunIm")),
            map(
                tuple((ws(vec(export)), ws(functiontype), ws(import))),
                |(export, _type, (m, f))| Function {
                    _type,
                    locals: Vec::new(),
                    body: Vec::new(),
                    init: ImportOrPresent::Import(m, f),
                    export,
                },
            ),
        )(input)
    }

    sexp(alt((function_import, function_present)))(input)
}

fn global(input: &str) -> IResult<&str, Global> {
    trace!("Parsing Global");
    fn global_mut(input: &str) -> IResult<&str, Global> {
        preceded(
            ws(tag("GlobMut")),
            map(tuple((ws(pretype), ws(vec(instr)))), |(pt, instrs)| {
                Global {
                    _type: GlobalType {
                        mutable: true,
                        _type: pt,
                    },
                    init: ImportOrPresent::Present(instrs),
                    export: Vec::new(),
                }
            }),
        )(input)
    }

    fn global_export(input: &str) -> IResult<&str, Global> {
        preceded(
            ws(tag("GlobEx")),
            map(
                tuple((ws(vec(export)), ws(pretype), ws(vec(instr)))),
                |(export, pt, instrs)| Global {
                    _type: GlobalType {
                        mutable: true,
                        _type: pt,
                    },
                    init: ImportOrPresent::Present(instrs),
                    export,
                },
            ),
        )(input)
    }

    fn global_import(input: &str) -> IResult<&str, Global> {
        preceded(
            ws(tag("GlobIm")),
            map(
                tuple((ws(vec(export)), ws(pretype), ws(import))),
                |(export, pt, (import_s1, import_s2))| Global {
                    _type: GlobalType {
                        mutable: true,
                        _type: pt,
                    },
                    init: ImportOrPresent::Import(import_s1, import_s2),
                    export,
                },
            ),
        )(input)
    }

    sexp(alt((global_mut, global_export, global_import)))(input)
}

fn module(input: &str) -> IResult<&str, Module> {
    trace!("Parsing Module");
    sexp(map(
        tuple((ws(vec(function)), ws(vec(global)), ws(table))),
        |(functions, globals, table)| Module {
            functions,
            table,
            globals,
        },
    ))(input)
}

pub(crate) fn parse_module(input: &str) -> Result<Module, String> {
    match ws(module)(input) {
        Ok((_, module)) => Ok(module),
        Result::Err(_err) => Err("Parsing failed".to_owned()),
    }
}

pub(crate) fn parse_modules(input: &str) -> Result<Vec<Module>, String> {
    trace!("Parsing Modules");
    match ws(vec(ws(module)))(input) {
        Ok((_, module)) => Ok(module),
        Result::Err(_err) => Err("Parsing failed".to_owned()),
    }
}

// TODO: modify tests so that we just have one from_file function
pub(crate) fn single_module_from_file(path: impl AsRef<std::path::Path>) -> Result<Module, String> {
    let data = fs::read_to_string(path).expect("Given path is not a valid file path");
    let module = parse_module(data.as_str())?;
    Ok(module)
}

pub(crate) fn multiple_modules_from_file(
    path: impl AsRef<std::path::Path>,
) -> Result<Vec<Module>, String> {
    let data: String = fs::read_to_string(path).expect("Given path is not a valid file path");
    let module = parse_modules(data.as_str())?;
    Ok(module)
}
