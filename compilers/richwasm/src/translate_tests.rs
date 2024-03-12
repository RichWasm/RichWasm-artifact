#![allow(unused_imports)]
use clap::builder::OsStr;
use wasabi_wasm as wasm;
use wasmtime::*;

use crate::rwasm::*;
use std::{collections::HashMap, fs, marker::PhantomData};

use crate::{translate_insts::FunctionContext, *};

#[test]
fn size_closure_test() {
    // Upper bounds
    // 0 = []                           => None
    // 1 = [Const 32, Var 0]            => min(Some(32), None) = Some(32)
    // 2 = [Const 64]                   => Some(64)
    // 3 = [Var 1, Plus(Var 2, Var 1)]  => min(Some(32), Plus(Some(64), Some(32)) = Some(32)
    // 4 = [Plus(Var 0, Var 0)]         => Plus(None, None) = None

    // Lower Bounds - no lower bounds

    let mut size_bounds: HashMap<u32, (Vec<Size>, Vec<Size>)> = HashMap::new();
    size_bounds.insert(0, (vec![], vec![]));
    size_bounds.insert(
        1,
        (
            vec![Size::Concrete(32), Size::Abstract(TypeVar(0, PhantomData))],
            vec![],
        ),
    );
    size_bounds.insert(2, (vec![Size::Concrete(64)], vec![]));
    size_bounds.insert(
        3,
        (
            vec![
                Size::Abstract(TypeVar(1, PhantomData)),
                Size::Plus(
                    Box::new(Size::Abstract(TypeVar(2, PhantomData))),
                    Box::new(Size::Abstract(TypeVar(1, PhantomData))),
                ),
            ],
            vec![],
        ),
    );
    size_bounds.insert(
        4,
        (
            vec![Size::Plus(
                Box::new(Size::Abstract(TypeVar(0, PhantomData))),
                Box::new(Size::Abstract(TypeVar(0, PhantomData))),
            )],
            vec![],
        ),
    );

    let closure = FunctionContext::get_size_closure(&size_bounds);
    let mut expected_closure = HashMap::new();
    expected_closure.insert(0, 32);
    expected_closure.insert(1, 32);
    expected_closure.insert(2, 64);
    expected_closure.insert(3, 32);
    expected_closure.insert(4, 32);

    assert_eq!(closure, expected_closure);
}

#[test]
fn load_allocator_with_memory() {
    let engine = Engine::default();
    let module = wasmtime::Module::from_file(&engine, "./src/allocator.wasm").expect("");

    let mut store = Store::new(&engine, ());

    // The allocator needs to import Memory.
    let memory_ty = MemoryType::new(2, None);
    let memory = Memory::new(&mut store, memory_ty).expect("msg");

    // No imported functions needed.
    let instance = Instance::new(&mut store, &module, &[memory.into()]).expect("msg");

    let main = instance
        .get_func(&mut store, "walloc")
        .expect("did not find alloc function");

    let mut wasm_results = vec![wasmtime::Val::I32(100)];
    let res = main.call(
        &mut store,
        &[wasmtime::Val::I32(64)],
        wasm_results.as_mut_slice(),
    );
    assert!(res.is_ok());
}

#[test]
fn import_allocator_into_module() {
    let engine = Engine::default();
    let allocator = wasmtime::Module::from_file(&engine, "./src/allocator.wasm").expect("");

    let mut store = Store::new(&engine, ());

    // The allocator needs to import Memory.
    let memory_ty = MemoryType::new(2, None);
    let memory = Memory::new(&mut store, memory_ty).expect("msg");

    // Allocator instance.
    let allocator_instance = Instance::new(&mut store, &allocator, &[memory.into()]).expect("msg");
    let walloc = allocator_instance.get_func(&mut store, "walloc").expect("");
    let wfree = allocator_instance.get_func(&mut store, "wfree").expect("");

    // r#"
    // (module
    //     (import "allocator" "walloc" (func $alloc (param i32) (result i32)))
    //     (import "allocator" "wfree" (func $free (param i32) (result)))
    //     (import "env" "memory" (memory (;0;) 2))
    //     (func (export "test") (param) (result i32)
    //         i32.const 64
    //         call $alloc
    //     )
    // )
    // "#
    let import_alloc = wasabi_wasm::Function::new_imported(
        wasabi_wasm::FunctionType::new(&[wasabi_wasm::ValType::I32], &[wasabi_wasm::ValType::I32]),
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
    let test_func = wasabi_wasm::Function::new(
        wasabi_wasm::FunctionType::new(&[], &[wasabi_wasm::ValType::I32]),
        wasabi_wasm::Code {
            locals: vec![],
            body: vec![
                wasabi_wasm::Instr::Const(wasabi_wasm::Val::I32(64)),
                wasabi_wasm::Instr::Call(wasabi_wasm::Idx::from(0_u32)),
                wasabi_wasm::Instr::End,
            ],
        },
        vec!["test".to_owned()],
    );
    let import_memory = wasabi_wasm::Memory::new_imported(
        wasabi_wasm::Limits {
            initial_size: 2,
            max_size: None,
        },
        "env".to_owned(),
        "memory".to_owned(),
    );

    let module = wasabi_wasm::Module {
        name: None,
        functions: vec![import_alloc, import_free, test_func],
        globals: vec![],
        tables: vec![],
        memories: vec![import_memory],
        start: None,
        custom_sections: vec![],
        metadata: wasabi_wasm::ModuleMetadata::default(),
    }
    .to_bytes()
    .expect("msg");

    let module = wasmtime::Module::from_binary(&engine, &module).expect("");

    let instance = Instance::new(
        &mut store,
        &module,
        &[walloc.into(), wfree.into(), memory.into()],
    )
    .expect("");

    let test = instance
        .get_func(&mut store, "test")
        .expect("did not find test function");

    let mut wasm_results = vec![wasmtime::Val::I32(100)];
    let res = test.call(&mut store, &[], wasm_results.as_mut_slice());
    assert!(res.is_ok());
}

#[allow(dead_code)]
fn run_module(
    path: impl AsRef<std::path::Path>,
    wasm_results: &mut [wasmtime::Val],
) -> Result<(), Error> {
    let engine = Engine::default();
    let allocator = wasmtime::Module::from_file(&engine, "./src/allocator.wasm")?;
    let mut store = Store::new(&engine, ());

    // The allocator needs to import Memory.
    let memory_ty = MemoryType::new(2, None);
    let memory = Memory::new(&mut store, memory_ty)?;

    // Instantiate the allocator and get the alloc and free functions.
    let allocator_instance = Instance::new(&mut store, &allocator, &[memory.into()])?;
    let walloc = allocator_instance
        .get_func(&mut store, "walloc")
        .expect("Could not find walloc function in allocator.");
    let wfree = allocator_instance
        .get_func(&mut store, "wfree")
        .expect("Could not find free function in allocator.");

    let rwasma = &rwasm::Module::from_file(path, true).unwrap()[0];
    let wasm_module = wasmtime::Module::from_binary(&engine, &rwasma.translate(0).to_bytes()?)?;

    let instance = Instance::new(
        &mut store,
        &wasm_module,
        &[walloc.into(), wfree.into(), memory.into()],
    )
    .expect("");

    let main = instance
        .get_func(&mut store, "main")
        .expect("did not find main function");

    let res = main.call(&mut store, &[], wasm_results);
    match res {
        Ok(_) => Ok(()),
        Err(e) => panic!("{e:?}"),
    }    

}

#[allow(dead_code)]
fn test_file(
    path: impl AsRef<std::path::Path>,
    wasm_results: &mut [wasmtime::Val],
    expected_results: &[i32],
) -> Result<(), anyhow::Error> {
    match run_module(path, wasm_results) {
        Ok(_) => (),
        Err(e) => panic!("{e} {:?}", e.source()),
    };

    let wasm_results = wasm_results
        .iter()
        .map(|val| match val.ty() {
            ValType::I32 => val.i32().unwrap() as i64,
            ValType::I64 => val.i64().unwrap(),
            ValType::F32 => val.f32().unwrap() as i64,
            ValType::F64 => val.f64().unwrap() as i64,
            _ => panic!("We are constrainted to I32, I64, F32, F64 in Wasm MVP."),
        })
        .collect::<Vec<_>>();

    itertools::assert_equal(
        &wasm_results,
        expected_results
            .iter()
            .map(|v| *v as i64)
            .collect::<Vec<_>>()
            .as_slice(),
    );

    Ok(())
}

#[test]
fn test_groups() {
    let tests_dir_path = "./tests/translation_tests/groups";
    for path in fs::read_dir(tests_dir_path).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        if extension.is_some_and(|e| e == "rwasma") {
            let mut wasm_results = vec![
                wasmtime::Val::I32(-1),
                wasmtime::Val::I32(-1),
                wasmtime::Val::I32(-1),
                wasmtime::Val::I64(-1),
                wasmtime::Val::I32(-1),
                wasmtime::Val::I64(-1),
                wasmtime::Val::I32(-1),
            ];

            test_file(path, &mut wasm_results, &[0, 1, 2, 3, 4, 5, 6]).unwrap();
        }
    }
}

#[test]
fn test_structs() {
    let tests_dir_path = "./tests/translation_tests/structs";
    for path in fs::read_dir(tests_dir_path).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        if extension.is_some_and(|e| e == "rwasma") {
            println!("{}", path.display());

            let mut wasm_results = vec![
                wasmtime::Val::I32(-1),
                wasmtime::Val::I32(-1),
                wasmtime::Val::I64(-1),
            ];

            test_file(path, &mut wasm_results, &[0, 1, 3]).unwrap();
        }
    }
}

#[test]
fn test_arrays() {
    let tests_dir_path = "./tests/translation_tests/arrays";
    for path in fs::read_dir(tests_dir_path).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        if extension.is_some_and(|e| e == "rwasma") {
            println!("{}", path.display());

            let mut wasm_results = vec![wasmtime::Val::I32(-1)];

            test_file(path, &mut wasm_results, &[12]).unwrap();
        }
    }
}

#[test]
fn test_function_calls() {
    let tests_dir_path = "./tests/translation_tests/function_calls";
    for path in fs::read_dir(tests_dir_path).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        if extension.is_some_and(|e| e == "rwasma") {
            let mut wasm_results = vec![wasmtime::Val::I32(-1)];

            test_file(path, &mut wasm_results, &[0]).unwrap();
        }
    }
}

 
 #[test]
 fn variant_0() {
     let mut wasm_results = vec![wasmtime::Val::I64(-1)];
     test_file(
         "./tests/translation_tests/variants/0_test_endstate.rwasma",
         &mut wasm_results,
         &[5],
     )
     .unwrap();
 }
 
 
 #[test]
 fn variant_1() {
     let mut wasm_results = vec![wasmtime::Val::I64(-1)];
     test_file(
         "./tests/translation_tests/variants/1_variant_simple.rwasma",
         &mut wasm_results,
         &[5],
     )
     .unwrap();
 }
 
 #[test]
 fn variant_2() {
     let mut wasm_results = vec![wasmtime::Val::I64(-1)];
     test_file(
         "./tests/translation_tests/variants/2_with_groups.rwasma",
         &mut wasm_results,
         &[0],
     )
     .unwrap();
 }
 
 
 #[test]
 fn el1() {
     let mut wasm_results = vec![wasmtime::Val::I64(-1)];
     test_file(
         "./tests/translation_tests/exists/1_exist_simple.rwasma",
         &mut wasm_results,
         &[5],
     )
     .unwrap();
 }
 