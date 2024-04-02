macro_rules! trace {
    ($($tt:tt)*) => {
        if cfg!(feature = "trace-log") {
            log::trace!($($tt)*);
        }
    };
}

pub mod parse;
pub mod parse_tests;
pub mod rwasm;
pub mod translate;
pub mod translate_insts;
pub mod translate_tests;

use std::{io, path::PathBuf};

use clap::Parser;

/// Compile RichWasm modules to WebAssembly.
#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File containing the RichWasm module to be compiled.
    #[arg(short, long)]
    file: String,

    /// Compile a single RichWasm module.
    #[arg(short, long)]
    single: bool,
    
    /// Name of wasm file to produce
    #[arg(short, long, default_value = None)]
    wasm_file: Option<String>,
}


#[allow(clippy::redundant_clone)]
fn main() -> io::Result<()> {
    let args = Args::parse();

    let path = args.file;
    let file = PathBuf::from(&path);
    let single_module = args.single;

    // FIXME: We don't want to just file clone, we want to dump to terminal. 
    // File clone means that we are over-writing the richwasm module being compiled 
    let wasm_file = &match args.wasm_file {
        Some(f) => PathBuf::from(f),
        None => file.clone(),
    };

    let rwasm_modules = rwasm::Module::from_file(&file, single_module).unwrap();

    for (ind, module) in rwasm_modules.iter().enumerate() {
        let wasm = module.translate(ind.to_string());

        let wasm_file = if single_module {
            wasm_file.clone()
        } else {
            let mut old_file_name = wasm_file
                .clone()
                .file_stem()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string();
            old_file_name.push('_');
            old_file_name.push_str(&ind.to_string());
            file.with_file_name(old_file_name)
        };

        let res = wasm.to_file(wasm_file);
        assert!(res.is_ok())
    }

    Ok(())
}
