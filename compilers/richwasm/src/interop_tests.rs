#![allow(unused_imports)]
use clap::builder::OsStr;
use wasabi_wasm as wasm;
use wasmtime::*;

use crate::rwasm::*;
use std::{collections::HashMap, fs, marker::PhantomData, path::Path, process::Command};

use crate::{translate_insts::FunctionContext, *};


#[allow(dead_code)]
fn build_compilers() {
    Command::new("dune")
        .args(["build", "l3", "ml", "rich_wasm"])
        .output()
        .expect("Failed to create output directory for ML compiler.");
}

#[allow(dead_code)]
fn compile_ml_file(
    ml_file_path: impl AsRef<std::path::Path>, 
    output_dir: impl AsRef<std::path::Path>
) {
    build_compilers();
    // Command to compile: _build/default/ml/rich_wasm_of_ml.exe -o example ml/examples/ml_compiler_example.ml
    // run {ML_COMPILER} -o {output_dir} {ml_file} 
    const ML_COMPILER : &str = "./../_build/default/ml/rich_wasm_of_ml.exe";
    let ml_file_path = ml_file_path.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of ML file path"));
    let output_dir = output_dir.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of output dir to store output of ML compiler"));
    Command::new("mkdir").args(["-p", output_dir]).output().expect("Failed to create output directory for ML compiler.");
    Command::new(ML_COMPILER)
        .args([
            "-o", 
            output_dir,
            ml_file_path
        ])
        .output()
        .expect(&format!("Failed to compile ML file {ml_file_path}"));
}

#[allow(dead_code)]
fn compile_l3_file(
    l3_file_path: impl AsRef<std::path::Path>, 
    output_dir: impl AsRef<std::path::Path>
) {
    build_compilers();
    // Command to compile: _build/default/l3/rich_wasm_of_l3.exe -o example l3/examples/l3_compiler_example.l3
    // run {L3_COMPILER} -o {output_dir} {l3_file} 
    const L3_COMPILER : &str = "./../_build/default/l3/rich_wasm_of_l3.exe";
    let l3_file_path = l3_file_path.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of L3 file path"));
    let output_dir = output_dir.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of output dir to store output of L3 compiler"));
    Command::new("mkdir").args(["-p", output_dir]).output().expect("Failed to create output directory for L3 compiler.");
    Command::new(L3_COMPILER)
        .args([
            "-o", 
            output_dir,
            l3_file_path
        ])
        .output()
        .expect(&format!("Failed to compile L3 file {l3_file_path}"));
}

#[allow(dead_code)]
fn run_rwasm_annotator(
    rwasm_dir: impl AsRef<std::path::Path>,
    rwasma_dir: impl AsRef<std::path::Path>
) {
    build_compilers();
    // Command to annotate: _build/default/rich_wasm/annotated_rich_wasm_of_rich_wasm.exe -o example -i example
    // run {ANNOTATOR} -o {output_dir} -i {input_dir} 
    const ANNOTATOR : &str = "./../_build/default/rich_wasm/annotated_rich_wasm_of_rich_wasm.exe";
    let input_dir = rwasm_dir.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of input_dir for annotator"));
    let output_dir = rwasma_dir.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of output dir to store output of annotator"));
    Command::new("mkdir").args(["-p", output_dir]).output().expect("Failed to create output directory for L3 compiler.");
    Command::new(ANNOTATOR)
        .args([
            "-o", 
            output_dir,
            "-i",
            input_dir
        ])
        .output()
        .expect(&format!("Failed to run annotator on .rwasm files in {input_dir}"));
}

#[allow(dead_code)]
fn run_richwasm_compiler(
    acc_module: (rwasm::Module, PathBuf), 
    main_module: (rwasm::Module, PathBuf), 
    output_dir: impl AsRef<std::path::Path>,
) -> Vec<(wasabi_wasm::Module, PathBuf)> {
    let wasm_modules = rwasm::Module::translate_modules(vec![
        acc_module, 
        main_module
    ]); 

    let output_dir_str = output_dir.as_ref().to_str().unwrap_or_else(|| panic!("Could not get str of output dir to store output of L3 compiler"));
    Command::new("mkdir").args(["-p", output_dir_str]).output().expect("Failed to create output directory for L3 compiler.");
    for (module, path) in &wasm_modules {
        let mut wasm_file_path = output_dir.as_ref().to_path_buf(); 
        wasm_file_path.push(path.file_stem().unwrap().to_str().unwrap());
        wasm_file_path.set_extension("wasm");
        module.to_file(wasm_file_path).unwrap_or_else(|_|panic!("WebAssembly encode error"));
    }

    wasm_modules
}

#[test]
fn test_ml_compiler() {
    let ml_file_path = "./../source_examples/ml_lists/main.ml";
    let output_dir = "./../source_examples/ml_lists/rwasm";
    compile_ml_file(ml_file_path, output_dir)
}

#[test]
fn test_l3_compiler() {
    let l3_file_path = "./../source_examples/l3_rolling_averages/main.l3";
    let output_dir = "./../source_examples/l3_rolling_averages/rwasm";
    compile_l3_file(l3_file_path, output_dir)
}

#[test]
fn test_annotator() {
    let rwasm_dir = "./../source_examples/ml_lists/rwasm";
    let rwasma_dir = "./../source_examples/ml_lists/rwasma";
    compile_ml_file("./../source_examples/ml_lists/main.ml", rwasm_dir);
    compile_ml_file("./../source_examples/ml_lists/list.ml", rwasm_dir);
    run_rwasm_annotator(rwasm_dir, rwasma_dir);
}

#[allow(dead_code)]
fn compile_and_run_annotator(
    dir_path: impl AsRef<std::path::Path>
) -> Vec<(rwasm::Module, PathBuf)> {

    let rwasm_dir = Path::new(dir_path.as_ref()).join("rwasm");
    for path in fs::read_dir(&dir_path).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        
        if extension.is_some_and(|e| e == "ml") {
            let ml_file_path = &path; 
            compile_ml_file(ml_file_path, &rwasm_dir); 
        }

        if extension.is_some_and(|e| e == "l3") {
            let ml_file_path = &path; 
            compile_l3_file(ml_file_path, &rwasm_dir); 
        }
    }    
 
    let rwasma_dir = Path::new(dir_path.as_ref()).join("rwasma"); 
    run_rwasm_annotator(rwasm_dir, &rwasma_dir);
    let mut rwasma_modules = vec![]; 

    for path in fs::read_dir(&rwasma_dir).unwrap() {
        let path = path.unwrap().path();
        let extension = path.extension().and_then(std::ffi::OsStr::to_str);
        if extension.is_some_and(|e| e == "rwasma") {            
            trace!("Parsing {}", path.clone().into_os_string().to_str().unwrap());
            let rwasmas = &rwasm::Module::from_file(&path, true)
                .expect(&format!("Parsing failed for rwasm file {}", path.clone().into_os_string().into_string().unwrap()) );
            for rwasma in rwasmas {
                rwasma_modules.push((
                    rwasma.clone(), 
                    path.clone()
                ))            
            }
        }    
    }
  
    rwasma_modules
}


#[test]
fn interop_example_1_fixed() {    
    let tests_dir_path = "./../source_examples/interop_example_1_fixed";    
    let rwasm_modules = compile_and_run_annotator(tests_dir_path);
    let (stash_module, main_module) = {
        if rwasm_modules[0].1.file_stem().unwrap() == "main" {
            (rwasm_modules[1].clone(), rwasm_modules[0].clone()) 
        } else {
            (rwasm_modules[0].clone(), rwasm_modules[1].clone()) 
        }
    };

    let wasm_modules = run_richwasm_compiler(
        stash_module,
        main_module,
        "./../source_examples/interop_example_1_fixed/wasm" 
    );
    let ((stash_module,_), (main_module, _)) = {
        if wasm_modules[0].1.file_stem().unwrap() == "main" {
            (wasm_modules[1].clone(), wasm_modules[0].clone()) 
        } else {
            (wasm_modules[0].clone(), wasm_modules[1].clone()) 
        }
    };
    
    // Initialize engine and load allocator 
    let engine = Engine::default();
    let allocator = wasmtime::Module::from_file(&engine, "./src/allocator.wasm").unwrap();
    let mut store = Store::new(&engine, ());

    // The allocator needs to import Memory.
    let memory_ty = MemoryType::new(2, None);
    let memory = Memory::new(&mut store, memory_ty).unwrap();
    
    // Instantiate the allocator and get the alloc and free functions.
    let allocator_instance = Instance::new(&mut store, &allocator, &[memory.into()]).unwrap();
    let walloc = allocator_instance
        .get_func(&mut store, "walloc")
        .expect("Could not find walloc function in allocator.");
    let wfree = allocator_instance
        .get_func(&mut store, "wfree")
        .expect("Could not find free function in allocator.");

    // Initialize stashed module 
    let initialized_stash_module = wasmtime::Module::from_binary(&engine, &stash_module.to_bytes().unwrap()).unwrap();
    let instance = Instance::new(
        &mut store,
        &initialized_stash_module,
        &[walloc.into(), wfree.into(), memory.into()],
    ).unwrap();

    // (export "stash" (func 2))
    // (export "get_stashed" (func 3))
    // (export "0" (global 0))

    let stash_func = instance
        .get_export(&mut store, "stash")
        .expect("Could not find stash function in stash.wasm.");

    let get_stashed_func = instance
        .get_export(&mut store, "get_stashed")
        .expect("Could not find get_stashed function in stash.wasm.");

    let global = instance
        .get_export(&mut store, "0")
        .expect("Could not find global0 in stash.wasm."); 

    // Instantiate main module     
    let wasm_module = wasmtime::Module::from_binary(&engine, &main_module.to_bytes().unwrap()).unwrap();
                
    // (import "allocator" "walloc" (func (;0;) (type 0)))
    // (import "allocator" "wfree" (func (;1;) (type 1)))
    // (import "stash" "stash" (func (;2;) (type 1)))
    // (import "stash" "get_stashed" (func (;3;) (type 2)))
    // (import "env" "memory" (memory (;0;) 2))
    // (import "stash" "0" (global (;0;) (mut i32)))              
    
    let instance = Instance::new(
        &mut store,
        &wasm_module,
        &vec![walloc.into(), wfree.into(), stash_func, get_stashed_func, memory.into(), global],
    );

    let mut wasm_results = vec![wasmtime::Val::I32(-1)];
    let main_func = instance
        .unwrap_or_else(|e|panic!("{}", e.to_string()))
        .get_func(&mut store, "main")
            .expect("Did not find main function");

    let res = main_func.call(&mut store, &[], &mut wasm_results);            

    match res {
        Ok(_) => {
            assert_eq!(wasm_results[0].i32().unwrap(), 0) 
        },
        Err(e) => panic!("{e:?}"),
    }    
    
}

#[allow(dead_code)]
fn interop_rolling_averages_no_ref_to_lin() {    
    let tests_dir_path = "./../source_examples/interop_rolling_averages_no_ref_to_lin";
    let rwasm_modules = compile_and_run_annotator(tests_dir_path);
    
    let (rolling_averages_module, main_module) = {
        if rwasm_modules[0].1.file_stem().unwrap() == "main" {
            (rwasm_modules[1].clone(), rwasm_modules[0].clone()) 
        } else {
            (rwasm_modules[0].clone(), rwasm_modules[1].clone()) 
        }
    };

    let wasm_modules = run_richwasm_compiler(
        rolling_averages_module,
        main_module,
        "./../source_examples/interop_rolling_averages_no_ref_to_lin/wasm" 
    );
    let ((rolling_averages_module,_), (main_module, _)) = {
        if wasm_modules[0].1.file_stem().unwrap() == "main" {
            (wasm_modules[1].clone(), wasm_modules[0].clone()) 
        } else {
            (wasm_modules[0].clone(), wasm_modules[1].clone()) 
        }
    };

    // Initialize engine and load allocator 
    let engine = Engine::default();
    let allocator = wasmtime::Module::from_file(&engine, "./src/allocator.wasm").unwrap();
    let mut store = Store::new(&engine, ());

    // The allocator needs to import Memory.
    let memory_ty = MemoryType::new(2, None);
    let memory = Memory::new(&mut store, memory_ty).unwrap();
    
    // Instantiate the allocator and get the alloc and free functions.
    let allocator_instance = Instance::new(&mut store, &allocator, &[memory.into()]).unwrap();
    let walloc = allocator_instance
        .get_func(&mut store, "walloc")
        .expect("Could not find walloc function in allocator.");
    let wfree = allocator_instance
        .get_func(&mut store, "wfree")
        .expect("Could not find free function in allocator.");

    // Initialize rolling_averages module 
    let initialized_rolling_averages_module = wasmtime::Module::from_binary(&engine, &rolling_averages_module.to_bytes().unwrap()).unwrap();
    let instance = Instance::new(
        &mut store,
        &initialized_rolling_averages_module,
        &[walloc.into(), wfree.into(), memory.into()],
    ).unwrap();
    
    // (export "new_" (func 3))
    // (export "free_" (func 4))
    // (export "add_sample" (func 5))
    // (export "average" (func 6))
    
    let new_ = instance
        .get_export(&mut store, "new_")
        .expect("Could not find new_ function in rolling_averages.wasm.");

    let free_ = instance
        .get_export(&mut store, "free_")
        .expect("Could not find free_ function in rolling_averages.wasm.");

    let add_sample = instance
        .get_export(&mut store, "add_sample")
        .expect("Could not find add_sample function in rolling_averages.wasm.");

    let average = instance
        .get_export(&mut store, "average")
        .expect("Could not find average function in rolling_averages.wasm.");

    // Instantiate main module     
    let wasm_module = wasmtime::Module::from_binary(&engine, &main_module.to_bytes().unwrap()).unwrap();

    // (import "allocator" "walloc" (func (;0;) (type 0)))
    // (import "allocator" "wfree" (func (;1;) (type 1)))
    // (import "rolling_averages" "new_" (func (;2;) (type 0)))
    // (import "rolling_averages" "free_" (func (;3;) (type 1)))
    // (import "rolling_averages" "add_sample" (func (;4;) (type 2)))
    // (import "rolling_averages" "average" (func (;5;) (type 3)))
    // (import "env" "memory" (memory (;0;) 2))
  
    let instance = Instance::new(
        &mut store,
        &wasm_module,
        &vec![walloc.into(), wfree.into(), new_, free_, add_sample, average, memory.into()],
    );

    let mut wasm_results = vec![wasmtime::Val::I32(-1)];
    let main_func = instance
        .unwrap_or_else(|e|panic!("{}", e.to_string()))
        .get_func(&mut store, "main")
            .expect("Did not find main function");

    let res = main_func.call(&mut store, &[], &mut wasm_results);            

    match res {
        Ok(_) => {
            assert_eq!(wasm_results[0].i32().unwrap(), 0) 
        },
        Err(e) => panic!("{e:?}"),
    }      

}