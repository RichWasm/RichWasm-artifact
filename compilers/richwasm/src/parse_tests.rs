#![allow(unused_imports)]
use std::marker::PhantomData;

use crate::rwasm::*;
use crate::{
    parse::{multiple_modules_from_file, single_module_from_file},
    *,
};

use lazy_static::lazy_static;

lazy_static! {
    static ref RICHWASM_MODULE_PARSING_TESTCASES: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( () () () )",
            "empty module"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "(
                () 
                () 
                () 
            )",
            "multiline in empty module"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{
                    entries: vec![
                        Ind::<Function>(1, PhantomData),
                        Ind::<Function>(2, PhantomData),
                        Ind::<Function>(3, PhantomData)] },
                globals: vec![]
            },
            "( () () (1 2 3) )",
            "table entries"
        ),
    ];
    static ref RICHWASM_GLOBALS_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Unit },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut Unit ())) () )",
            "Mutable rwasm::Globals"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Unit },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut Unit ())) () )",
            "Mutable rwasm::Globals"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: false, _type: PreType::Unit },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec!["glob".to_owned()]
                }]
            },
            "( () ((GlobEx (glob) Unit ())) () )",
            "exported globals"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: false, _type: PreType::Unit },
                        init: ImportOrPresent::Import("foo".to_string(), "bar".to_string()),
                        export: vec!["glob".to_owned()]
                }]
            },
            "( () ((GlobIm (glob) Unit (Import foo bar))) () )",
            "imported globals"
        ),
    ];
    static ref RICHWASM_TYPES_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
            (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Unit },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut Unit ())) () )",
            "Pretype Unit"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Constant(ConstType::I32(Sign::U)) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Num (Int U I32)) ())) () )",
            "Pretype Num Int Unsigned I32"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Constant(ConstType::I64(Sign::S)) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Num (Int S I64)) ())) () )",
            "Pretype Num Int Signed I64"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Constant(ConstType::F32) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Num (Float F32)) ())) () )",
            "Pretype Num Float F32"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Constant(ConstType::F64) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Num (Float F64)) ())) () )",
            "Pretype Num Float F64"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Var(TypeVar(0, PhantomData)) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Var 0) ())) () )",
            "Pretype Var"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::Product(vec![]) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Prod ()) ())) () )",
            "Pretype Product"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{ mutable: true, _type: PreType::CodeRef(FunctionType { params: vec![], results: vec![], vardecl: vec![] }) },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Coderef (() (()()))) ())) () )",
            "Pretype Coderef"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Rec(Qual::Lin, Type(Box::new(PreType::Unit), Qual::Lin))
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Rec (QualC Lin) (Unit (QualC Lin))) ())) () )",
            "Pretype Rec with QualC Lin"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Rec(Qual::GC, Type(Box::new(PreType::Unit), Qual::Lin))
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Rec (QualC Unr) (Unit (QualC Lin))) ())) () )",
            "Pretype Rec with QualC Unr"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Rec(Qual::Var(TypeVar(0, PhantomData)), Type(Box::new(PreType::Unit), Qual::Lin))
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Rec (QualV 0) (Unit (QualC Lin))) ())) () )",
            "Pretype Rec with QualV"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Ptr(Loc { _abstract: TypeVar(0, PhantomData) })
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Ptr (LocV 0)) ())) () )",
            "Pretype Ptr with Loc"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::ExLoc(Type(Box::new(PreType::Unit), Qual::Lin))
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (ExLoc (Unit (QualC Lin))) ())) () )",
            "Pretype Exloc"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Own(Loc { _abstract: TypeVar(0, PhantomData) })
                        },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Own (LocV 0)) ())) () )",
            "Pretype Own"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Variant(vec![]))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Variant ())) ())) () )",
            "Pretype Cap with HeapType Variant"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Struct(vec![]))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Struct ())) ())) () )",
            "Pretype Cap with HeapType Struct"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Array(Type(Box::new(PreType::Unit), Qual::Lin)))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Array (Unit (QualC Lin)))) ())) () )",
            "Pretype Cap with HeapType Struct"
        ),

        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Exists(
                                    Qual::Lin,
                                    Size::Concrete(0),
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Ex (QualC Lin) (SizeC 0) (Unit (QualC Lin)))) ())) () )",
            "Pretype Cap with HeapType Exists"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Ref(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Struct(vec![]))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Ref R (LocV 0) (Struct ())) ())) () )",
            "Pretype Ref"
        ),
    ];
    static ref RICHWASM_SIZE_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Exists(
                                    Qual::Lin,
                                    Size::Concrete(0),
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Ex (QualC Lin) (SizeC 0) (Unit (QualC Lin)))) ())) () )",
            "Concrete Size"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Exists(
                                    Qual::Lin,
                                    Size::Abstract(TypeVar(0, PhantomData)),
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Ex (QualC Lin) (SizeV 0) (Unit (QualC Lin)))) ())) () )",
            "Abstract Size"
        ),
        (
            rwasm::Module{
                functions: vec![],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![
                    rwasm::Global{
                        _type: rwasm::GlobalType{
                            mutable: true,
                            _type: PreType::Cap(
                                Cap::Read,
                                Loc { _abstract: TypeVar(0, PhantomData) },
                                HeapType::Exists(
                                    Qual::Lin,
                                    Size::Plus(
                                        Box::new(Size::Concrete(0)),
                                        Box::new(Size::Abstract(TypeVar(0, PhantomData)))
                                    ),
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ))
                            },
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }]
            },
            "( () ((GlobMut (Cap R (LocV 0) (Ex (QualC Lin) (SizeP (SizeC 0) (SizeV 0)) (Unit (QualC Lin)))) ())) () )",
            "Plus Size"
        ),
    ];
    static ref RICHWASM_FUNCTION_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ())) () () )",
            "empty function with function type"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] },
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( (
                (Fun () (() (() ())) () ())
                (Fun () (() (() ())) () ())
            ) () () )",
            "multiple functions"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![Type(Box::new(PreType::Unit), Qual::Lin)],
                            results: vec![Type(Box::new(PreType::Unit), Qual::Lin)],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (((Unit (QualC Lin))) ((Unit (QualC Lin))))) () ())) () () )",
            "Parsing Function Type with parameters and results failed."
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Loc]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Loc)) (() ())) () ())) () () )",
            "Function Type with Loc KindVar"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Qual(
                                vec![Qual::Lin],
                                vec![Qual::GC]
                        )]},
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Qual ((QualC Lin)) ((QualC Unr)))) (() ())) () ())) () () )",
            "Function Type with Qual KindVar"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Size(
                                vec![Size::Concrete(0)],
                                vec![Size::Abstract(TypeVar(0, PhantomData))])]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Size ((SizeC 0)) ((SizeV 0)) )) (() ())) () ())) () () )",
            "Function Type with Size KindVar"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Type(
                                Qual::Lin,
                                Size::Concrete(0),
                                HeapableConst::Heapable
                        )]},
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Type (QualC Lin) (SizeC 0) Heapable)) (() ())) () ())) () () )",
            "Function Type with Type KindVar"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Type(
                                Qual::Lin,
                                Size::Concrete(0),
                                HeapableConst::Heapable
                        )]},
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Type (QualC Lin) (SizeC 0) Heapable)) (() ())) () ())) () () )",
            "Heapable HeapConst"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![VarDecl::Type(
                                Qual::Lin,
                                Size::Concrete(0),
                                HeapableConst::NotHeapable
                        )]},
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (((Type (QualC Lin) (SizeC 0) NotHeapable)) (() ())) () ())) () () )",
            "Function Type with Size KindVar"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![
                            "foo1".to_owned(),
                            "bar".to_owned()]
                }],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun (foo1 bar) (() (() ())) () ())) () () )",
            "Function Type with parameters and results"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![
                            Size::Concrete(0),
                            Size::Abstract(TypeVar(0, PhantomData)),
                            Size::Plus(
                                Box::new(Size::Concrete(0)),
                                Box::new(Size::Abstract(TypeVar(0, PhantomData)))
                            )
                        ],
                        body: vec![],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![]
                }],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) ((SizeC 0) (SizeV 0) (SizeP (SizeC 0) (SizeV 0))) ())) () () )",
            "Function Type with parameters and results"
        ),
    ];
    static ref RICHWASM_INSTRUCTION_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Unit
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IVal Unit)))) () () )",
            "Unit Instructtion"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Constant(ConstType::I32(Sign::U), 0),
                            Instr::Constant(ConstType::I32(Sign::U), 1)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (IVal (Num (Int U I32) (Second 0)))
                (IVal (Num (Int U I32) (Second 1)))
            ))) () () )",
            "Num Instructtion"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Unreachable
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (IUnreachable))) () () )",
            "Unreachable Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Nop
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (INop))) () () )",
            "Nop Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Drop
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (IDrop))) () () )",
            "Drop Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Select
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (ISelect))) () () )",
            "Select Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Block(
                                BlockType { params: vec![], results: vec![] },
                                LocalEffect(vec![]),
                                vec![]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IBlock (() ()) () () 
            )))) () () )",
            "Block Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Loop(
                                BlockType { params: vec![], results: vec![] },
                                vec![]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ILoop (() ()) () 
            )))) () () )",
            "Loop Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::IfThenElse(
                                BlockType { params: vec![], results: vec![] },
                                LocalEffect(vec![]),
                                vec![],
                                vec![]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IITE (() ()) () () () 
            )))) () () )",
            "If Then Else Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Br(0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IBr 0 
            )))) () () )",
            "Br Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::BrIf(0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IBr_if 0 
            )))) () () )",
            "BrIf Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::BrTable(
                                0,
                                vec![0, 1, 2, 3, 4, 5, 8]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IBr_table (0 1 2 3 4 5 8) 0 
            )))) () () )",
            "BrTable Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Return
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IRet
            ))) () () )",
            "Ret Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Local(
                                LocalOp::Tee(
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ),
                                0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ITee_local 0 (Unit (QualC Lin))
            )))) () () )",
            "Tee Local Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Local(
                                LocalOp::Get(
                                    Qual::Lin,
                                    PreType::Unit
                                ),
                                0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IGet_local 0 (QualC Lin) Unit
            )))) () () )",
            "Get Local Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Local(
                                LocalOp::Set(
                                    Type(Box::new(PreType::Unit), Qual::Lin)
                                ),
                                0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ISet_local 0 (Unit (QualC Lin))
            )))) () () )",
            "Set Local Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Global(rwasm::GlobalOp::Get, 0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IGet_global 0
            )))) () () )",
            "Get rwasm::Global Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Global(rwasm::GlobalOp::Set, 0)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ISet_global 0
            )))) () () )",
            "Set rwasm::Global Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::CodeRef(Ind::<Function>(0, PhantomData))
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ICoderefI 0
            )))) () () )",
            "Coderef Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Inst(vec![])
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IInst ()
            )))) () () )",
            "Inst Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::CallIndirect(BlockType {
                                params: vec![],
                                results: vec![],
                            })],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ICall_indirect (() ())
            )))) () () )",
            "Call Indirect Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Call(
                                Ind::<Function>(0, PhantomData),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                ICall 0 ()
            )))) () () )",
            "Call Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::RecFold(
                                PreType::Unit
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IRecFold Unit
            )))) () () )",
            "RecFold Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::RecUnfold
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IRecUnfold
            ))) () () )",
            "RecUnfold Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Group(
                                0,
                                Qual::Lin
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IGroup 0 (QualC Lin)
            )))) () () )",
            "Group Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::UnGroup
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IUngroup
            ))) () () )",
            "UnGroup Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::CapSplit
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                ICapSplit
            ))) () () )",
            "CapSplit Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::CapJoin
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                ICapJoin
            ))) () () )",
            "CapJoin Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::RefDemote
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IRefDemote
            ))) () () )",
            "RefDemote Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::MemPack(Loc { _abstract: TypeVar::<Loc>(0, PhantomData) })
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IMemPack (LocV 0)
            )))) () () )",
            "MemPack Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::MemUnpack(
                                BlockType { params: vec![], results: vec![] },
                                LocalEffect(vec![]),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IMemUnpack (() ()) () ()
            )))) () () )",
            "MemUnPack Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Struct(
                                StructOp::Malloc(vec![], Qual::Lin),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IStructMalloc () (QualC Lin) ()
            )))) () () )",
            "StructMalloc Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Struct(
                                StructOp::Free,
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IStructFree ()
            )))) () () )",
            "StructFree Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Struct(
                                StructOp::Get(0),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IStructGet 0 ()
            )))) () () )",
            "StructGet Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Struct(
                                StructOp::Set(0),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IStructSet 0 ()
            )))) () () )",
            "StructSet Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Struct(
                                StructOp::Swap(0),
                                vec![]
                            )],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IStructSwap 0 ()
            )))) () () )",
            "StructSwap Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::VariantMalloc(
                                0,
                                vec![],
                                Qual::Lin
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IVariantMalloc 0 () (QualC Lin)
            )))) () () )",
            "Variant Malloc Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::VariantCase(
                                Qual::Lin,
                                vec![],
                                BlockType { params: vec![], results: vec![] },
                                LocalEffect(vec![]),
                                vec![]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IVariantCase (QualC Lin) () (() ()) () () 
            )))) () () )",
            "Variant Case Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Array(
                                ArrayOp::Malloc(
                                    Qual::Lin),
                                    Type(Box::new(PreType::Unit), Qual::Lin))
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IArrayMalloc (QualC Lin) (Unit (QualC Lin))
            )))) () () )",
            "Array Malloc Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Array(
                                ArrayOp::Get,
                                Type(Box::new(PreType::Unit), Qual::Lin))
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IArrayGet (Unit (QualC Lin))
            )))) () () )",
            "Array Get Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Array(
                                ArrayOp::Set,
                                Type(Box::new(PreType::Unit), Qual::Lin))
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IArraySet (Unit (QualC Lin))
            )))) () () )",
            "Array Set Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Array(
                                ArrayOp::Free,
                                Type(Box::new(PreType::Unit), Qual::Lin))
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IArrayFree (Unit (QualC Lin))
            )))) () () )",
            "Array Free Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::ExistPack(
                                PreType::Unit,
                                HeapType::Variant(vec![]),
                                Qual::Lin)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IExistPack Unit (Variant ()) (QualC Lin)
            )))) () () )",
            "Exist Pack Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::ExistUnpack(
                                Qual::Lin,
                                BlockType{ params: vec![], results: vec![] },
                                LocalEffect(vec![]),
                                vec![],
                                Type(Box::new(PreType::Unit), Qual::Lin)
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IExistUnpack (QualC Lin) (()()) () () (Unit (QualC Lin))
            )))) () () )",
            "Exist UnPack Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::RefSplit
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IRefSplit
            ))) () () )",
            "Ref Split Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::RefJoin
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                IRefJoin
            ))) () () )",
            "Ref Join Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Qualify(Qual::Lin)
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((
                IQualify (QualC Lin)
            )))) () () )",
            "Qualify Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Block(
                                BlockType { params: vec![], results: vec![] },
                                LocalEffect(vec![
                                    (Ind::<Local>(0, PhantomData), Type(Box::new(PreType::Unit), Qual::Lin)),
                                    (Ind::<Local>(1, PhantomData), Type(Box::new(PreType::Unit), Qual::Lin)),
                                ]),
                                vec![]
                            )
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IBlock (() ()) (
                    (0 (Unit (QualC Lin)))
                    (1 (Unit (QualC Lin)))
                ) () 
            )))) () () )",
            "LocalEffects Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32Clz)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32Ctz)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32Popcnt)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64Clz)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64Ctz)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64Popcnt)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Iu I32 Iclz))
                (INe (Iu I32 Ictz))
                (INe (Iu I32 Ipopcnt))
                (INe (Iu I64 Iclz))
                (INe (Iu I64 Ictz))
                (INe (Iu I64 Ipopcnt))
            ))) () () )",
            "Numeric Integer Unary Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32Add)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32Sub)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32DivS)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32DivU)),

                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64Add)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64Sub)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64DivS)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64DivU)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Ib I32 Iadd))
                (INe (Ib I32 Isub))
                (INe (Ib I32 S Idiv))
                (INe (Ib I32 U Idiv))
                
                (INe (Ib I64 Iadd))
                (INe (Ib I64 Isub))
                (INe (Ib I64 S Idiv))
                (INe (Ib I64 U Idiv))
            ))) () () )",
            "Numeric Integer Binary Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32Abs)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32Neg)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32Trunc)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64Abs)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64Neg)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64Trunc)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Fu F32 Iabs))
                (INe (Fu F32 Ineq))
                (INe (Fu F32 Itrunc))
                (INe (Fu F64 Iabs))
                (INe (Fu F64 Ineq))
                (INe (Fu F64 Itrunc))
            ))) () () )",
            "Numeric Float Unary Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Add)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Div)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Min)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Add)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Div)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Min)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Fb F32 Iaddf))
                (INe (Fb F32 Idivf))
                (INe (Fb F32 Imin))
                (INe (Fb F64 Iaddf))
                (INe (Fb F64 Idivf))
                (INe (Fb F64 Imin))
            ))) () () )",
            "Numeric Float Binary Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32Eqz)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64Eqz)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (It I32 Ieqz))
                (INe (It I64 Ieqz))
            ))) () () )",
            "Numeric Integer test Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32Eq)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32Ne)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32LtS)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I32LtU)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64Eq)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64Ne)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64LtS)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::I64LtU)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Ir I32 Ieq))
                (INe (Ir I32 Ine))
                (INe (Ir I32 S Ilt))
                (INe (Ir I32 U Ilt))
                (INe (Ir I64 Ieq))
                (INe (Ir I64 Ine))
                (INe (Ir I64 S Ilt))
                (INe (Ir I64 U Ilt))
            ))) () () )",
            "Numeric Integer Compare (Ir) Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Eq)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Ne)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F32Lt)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Eq)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Ne)),
                            Instr::Numeric(NumericInstr::Binary(BinaryOp::F64Lt)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Fr F32 Ieqf))
                (INe (Fr F32 Inef))
                (INe (Fr F32 Iltf))
                (INe (Fr F64 Ieqf))
                (INe (Fr F64 Inef))
                (INe (Fr F64 Iltf))
            ))) () () )",
            "Numeric Float Compare (Ir) Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32WrapI64)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32ReinterpretF32)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32TruncF32S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32TruncF32U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32TruncF64S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I32TruncF64U)),

                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64ExtendI32S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64ExtendI32U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64ReinterpretF64)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64TruncF32S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64TruncF32U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64TruncF64S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::I64TruncF64U)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (Cvt I32 IWrap I64))
                (INe (Cvt I32 IReinterpret F32))
                (INe (Cvt I32 ITrunc F32 S))
                (INe (Cvt I32 ITrunc F32 U))
                (INe (Cvt I32 ITrunc F64 S))
                (INe (Cvt I32 ITrunc F64 U))

                (INe (Cvt I64 IExtend I32 S))
                (INe (Cvt I64 IExtend I32 U))
                (INe (Cvt I64 IReinterpret F64))
                (INe (Cvt I64 ITrunc F32 S))
                (INe (Cvt I64 ITrunc F32 U))
                (INe (Cvt I64 ITrunc F64 S))
                (INe (Cvt I64 ITrunc F64 U))
            ))) () () )",
            "Numeric Integer Cvt Instructions"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32ConvertI32S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32ConvertI32U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32ConvertI64S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32ConvertI64U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32ReinterpretI32)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F32DemoteF64)),

                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64ConvertI32S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64ConvertI32U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64ConvertI64S)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64ConvertI64U)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64ReinterpretI64)),
                            Instr::Numeric(NumericInstr::Unary(UnaryOp::F64PromoteF32)),
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () (
                (INe (CvtF F32 IConvert I32 S))
                (INe (CvtF F32 IConvert I32 U))
                (INe (CvtF F32 IConvert I64 S))
                (INe (CvtF F32 IConvert I64 U))
                (INe (CvtF F32 IReinterpret I32))
                (INe (CvtF F32 IDemote F64))

                (INe (CvtF F64 IConvert I32 S))
                (INe (CvtF F64 IConvert I32 U))
                (INe (CvtF F64 IConvert I64 S))
                (INe (CvtF F64 IConvert I64 U))
                (INe (CvtF F64 IReinterpret I64))
                (INe (CvtF F64 IPromote F32))
                
            ))) () () )",
            "Numeric Integer Cvt Instructions"
        ),
    ];
    static ref RICHWASM_INDEX_PARSING: Vec<(rwasm::Module, &'static str, &'static str)> = vec![
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Inst(vec![
                                Index::Loc(Loc {
                                    _abstract: TypeVar(0, PhantomData) }),
                                Index::Loc(Loc {
                                    _abstract: TypeVar(1, PhantomData) }),
                            ])
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IInst (
                (LocI (LocV 0)) (LocI (LocV 1))
            ) )))) () () )",
            "Loc VarInst/Index Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Inst(vec![
                                Index::Size(Size::Concrete(0))
                            ])
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IInst (
                (SizeI (SizeC 0))
            ) )))) () () )",
            "Size VarInst/Index Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Inst(vec![
                                Index::Qual(Qual::Lin)
                            ])
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IInst (
                (QualI (QualC Lin))
            ) )))) () () )",
            "Qual VarInst/Index Instruction"
        ),
        (
            rwasm::Module{
                functions: vec![
                    Function{
                        _type: FunctionType {
                            params: vec![],
                            results: vec![],
                            vardecl: vec![]
                        },
                        locals: vec![],
                        body: vec![
                            Instr::Inst(vec![
                                Index::PreType(PreType::Unit)
                            ])
                        ],
                        init: ImportOrPresent::Present(vec![]),
                        export: vec![] }
                ],
                table: rwasm::Table{ entries: vec![] },
                globals: vec![]
            },
            "( ((Fun () (() (() ())) () ((IInst (
                (PretypeI Unit)
            ) )))) () () )",
            "Pretype VarInst/Index Instruction"
        )
    ];
}

#[test]
fn parse_module_tests() {
    let parse_testcases = RICHWASM_MODULE_PARSING_TESTCASES.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_globals_tests() {
    let parse_testcases = RICHWASM_GLOBALS_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_types_tests() {
    let parse_testcases = RICHWASM_TYPES_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_size_tests() {
    let parse_testcases = RICHWASM_SIZE_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_function_tests() {
    let parse_testcases = RICHWASM_FUNCTION_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_instruction_tests() {
    let parse_testcases = RICHWASM_INSTRUCTION_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}

#[test]
fn parse_index_tests() {
    let parse_testcases = RICHWASM_INDEX_PARSING.iter();
    for (i, (richwasm, text, msg)) in parse_testcases.enumerate() {
        let parsed = parse::parse_module(text);
        match parsed {
            Err(err) => {
                println!("\ntest #{i} could not be parsed\ninput: `{text}`\nerr: `{err}`\n{msg}")
            }
            Ok(parsed) => {
                assert_eq!(&parsed, richwasm, "\ntest #{i}\ninput: `{text}`\n{msg}")
            }
        };
    }
}
