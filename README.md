# RichWasm: Bringing Safe, Fine-Grained, Shared-Memory Interoperability Down to WebAssembly

This repository contains supplementary material for the paper "RichWasm: Bringing Safe, Fine-Grained, Shared-Memory Interoperability Down to WebAssembly" (PLDI'24).

## Running via Docker

### Building the Image
To build the artifact, simply run: 
```
git clone git@github.com:RichWasm/RichWasm-artifact.git
cd RichWasm-artifact
docker build -t richwasm .
```
The image itself is about 13 GB on disk and takes roughly 30 minutes to build, depending on hardware and network connection.

### Running the Image 

To connect to the container, run 
```
docker run -it richwasm
```

### Running a pre-built image 

We have provided a pre-built docker image on [DockerHub](https://hub.docker.com/r/richwasm/richwasm-artifact-image). Get the container running with the following commands.
```
# Pull Docker image from DockerHub
docker pull richwasm/richwasm-artifact-image

# Run a container with the image
docker run -it richwasm/richwasm-artifact-image:latest
```

### Container structure 

The container is organized as follows.

- `/home/richwasm/`
  - `compilers/`: Compilers described in the paper. 
    - `ml/`: Compiler from ML to RichWasm along with compiler specific tests. 
    - `l3/`: Compiler from L3 to RichWasm along with compiler specific tests. 
    - `rich_wasm/`: Typechecker and annotater for RichWasm code produced by the above compilers. 
    - `richwasm/`: Compiler from RichWasm to WebAssembly. 
    - `source_examples/`: Examples of ML and L3 code interoperating and being typechecked. 
  - `coq-proofs/`: Progress and Preservation proofs for RichWasm's type system. 

## What is this Artifact? 

This artifact is a self-contained environment to reproduce the claims in the PLDI'24 paper "RichWasm: Bringing Safe, Fine-Grained, Shared-Memory Interoperability Down to WebAssembly". This artifact contains, 
- A mechanized proof of RichWasm's type safety
- Compilers from ML and L3 to RIchWasm
- An annotator and type checker for RichWasm code
- A compiler from RichWasm to WebAssembly. 
This artifact can be used to compile the proofs, use the various compilers and run and inspect their tests. 

## Coq Proofs

To compile the proofs, run the following commands in the docker container. Compiling the proofs takes somewhere between 10 and 30 minutes, depending on hardware. 
```
cd /home/RichWasm/coq-proof
eval $(opam env --switch=4.08.1)    // switch to the right version of the OCaml compiler 
make
```
Your output might contain a few warnings but should not have any errors. 

### Structure of Proofs Directory

- `tactics.v` `EnsembleUtil.v` `functions.v` `list_util.v` `map_util.v`: Generic helper libraries
- `term.v`: Syntax of RichWasm
- `debruijn.v`: Generic definitions of substitutions and related operations for DeBruijn indices
- `subst.v`: Instantiation of the generic DeBruijn operations for the RichWasm language
- `memory.v`: Definition of the memory model as a Coq module
- `locations.v`: Definition of reachability and specification of GC
- `reduction.v`: Definition of the reduction relation
- `typing.v`: Definitions of the various typing judgments
- `splitting.v`: Formalization of the disjoint union operation of the linear memory typing
- `surface.v`: Formalization of well-formedness predicates for surface source programs
- `typing_util.v`: Miscellaneous lemmas for the typing judgments
- `misc_util.v`: Miscellaneous lemmas about substitutions, mostly related to preservation of typing
- `hti_subst_indices.v`: Lemmas stating that instruction typing is preserved under valid substitutions
- `progress.v`: Progress proof
- `preservation.v`: Preservation proof of instruction typing for the reduction rules that do no involve the heap
- `preservation_full.v`: Preservation proof of instruction typing for the reduction rules that involve the heap
- `preservation_GC.v`: Preservation proof of instruction typing for the GC rule of the reduction relation
- `safety.v`: Top-level theorem for type safety

### Definitions and Theorems

For each definition and theorem that appears in the paper, we give a pointer to the corresponding location in the code.

#### Section 2

- (Pre)types (pg 5, fig. 2): `term.v` lines 71-85
- Values (pg 5, fig. 2): `term.v` line 121
- Heap values (pg 5, fig. 2): `term.v` line 133
- Instructions (pg 5, fig. 2): `term.v` line 216
- Functions (pg 5, fig. 2): `term.v` line 297
- Globals (pg 5, fig. 2): `term.v` line 306
- Modules (pg 5, fig. 2): `term.v` line 311

#### Section 3

The reduction relation is split across few relations each one representing reduction steps

- Reduction steps that do not involve the heap:  `Reduce_simple`, file `reduction.v` line 211
- Reduction steps that involve the heap: `Reduce_full`, file `reduction.v` line 451
- Reduction relation with congruence rules: `Reduce`, file `reduction.v` line 615
- Garbage-collection step: `GC_step`, file `reduction.v` line 659
- Top-level reduction relation:`Reduce_GC`, file `reduction.v` line 682

#### Section 4

- Local environment: `Local_Ctx`, file `typing.v` line 447
- Function environment: `Function_Ctx`, file `typing.v` line 449
- Module environment: `Module_Ctx`, file `typing.v` line 441
- Store typing: `StoreTyping`, file `typing.v` line 702
- Value typing: `HasTypeValue`, file `typing.v` line 1509
- Instruction typing: `HasTypeInstruction`, file `typing.v` line 1861
- Store typing: `HasTypeStore`, file `typing.v` line 3554
- Configuration typing: `HasTypeConfig, file `typing.v` line 3563

- Top-level progress theorem: `Progress`, file `progress.v` line 2598
- Top-level preservation theorem: `Preservation`, file `safety.v` line 2674

We also prove a top-level soundness theorem (not shown in the paper): `Soundness`, file `safety.v` line 2796 

### Remaining Admits

At the time of submitting this artifact, there is one remaining admit in the file `hti_subst_indices.v`, named `HasTypeInstruction_subst_index`.

It says that for well-typed instructions `S; M; F; L |- es : tau_1* -> tau_2* | L'` and a concrete instantiation `I` of a kind variable `rho` where `I` satisfies the constraints of `rho`, the typing judgement still holds after substituting `rho` with `I`, that is,
```
S; M; F[I/rho]; L[I/rho] |- es[I/rho] : tau_1[I/rho]* -> tau_2[I/rho]* | L'[I/rho].
```

We are confident that we will prove this shortly after the deadline. Note that most of the substitution lemmas we need have already been proved in `misc_util.v`


## Compilers 

This directory contains the compilers from ML and L3 to RichWasm, a RichWasm typechecker, and a compiler from RichWasm to Wasm. The ML compiler, L3 compiler, and RichWasm typechecker are written in OCaml. To run these compilers and check that their tests pass, run the following commands
```
cd /home/RichWasm/compilers 
eval $(opam env --switch=5.0.0)     // switch to the right version of the OCaml compiler 
dune build ml l3 rich_wasm          // build compilers from source 
dune runtest ml l3 rich_wasm        // run all tests 
```
The last command should run without any errors. If no output is seen, the tests have all passed successfully. 

To run the compiler from RichWasm to Wasm and to make sure its tests are passing, run the following commands, 
```
cd /home/RichWasm/compilers/richwasm
cargo test
```
The output on the screen should look as follows. Not that each of these reports are for a collection of tests, rather than a single test. 
```
running tests
test parse_tests::parse_globals_tests ... ok
test parse_tests::parse_module_tests ... ok
test parse_tests::parse_size_tests ... ok
test parse_tests::parse_function_tests ... ok
test parse_tests::parse_index_tests ... ok
test translate_tests::size_closure_test ... ok
test parse_tests::parse_types_tests ... ok
test parse_tests::parse_instruction_tests ... ok
...
```
Note that you have to build the ML, L3 compilers and RichWasm annotator before running the tests for the RichWasm compiler. This is because we have some end to end tests that need the entire compiler pipeline to be setup.


### Structure of Compilers Directory
- `ml/`: Compiler from ML to RichWasm.
    - `syntax.ml`: Abstract syntax for each phase of the compiler.
    - `parse.ml`: Parser for ML. A comment describing the grammar is included at the bottom.
    - `tagging.ml` and `source_printer.ml`: Annotate the tree with some extra information to improve typechecking errors (e.g. recover variable names after the debruijn transformation).
    - `debruijn.ml`: Transforms variable names into debruijn indices.
    - `typecheck.ml`: Typechecks ML.
    - `hoist.ml`: Performs closure conversion and hoists all functions to the top-level.
    - `annotate.ml`: Annotates programs with size/qual information needed by RichWasm.
    - `codegen.ml`: Produces RichWasm code.
    - `ml.ml`: Combines all phases.
    - `rich_wasm_of_ml.ml`: Creates an executable which can be used to compile ML files to RichWasm.
- `l3/`: Compiler from L3 to RichWasm.
    - `syntax.ml`: Abstract syntax for each phase of the compiler.
    - `parse.ml`: Parser for L3. A comment describing the grammar is included at the bottom.
    - `tagging.ml` and `source_printer.ml`: Annotate the tree with some extra information to improve typechecking errors (e.g. recover variable names after the debruijn transformation).
    - `debruijn.ml`: Transforms variable names into debruijn indices.
    - `typecheck.ml`: Typechecks L3.
    - `codegen.ml`: Produces RichWasm code.
    - `l3.ml`: Combines all phases.
    - `rich_wasm_of_l3.ml`: Creates an executable which can be used to compile L3 files to RichWasm.
- `rich_wasm/`: RichWasm typechecker and annotator (annotated RichWasm is then compiled to WebAssembly with the compiler described in the next bullet).
    - `rich_wasm.ml`: Syntax of RichWasm.
    - `rich_wasm_compiler_interface.ml`: Syntax of annotated RichWasm, which contains additional type information (discovered during typechecking) needed by the RichWasm compiler described below.
    - `substitution.ml`: Functions for performing substitution of various kinds (qual, size, type, loc) on RichWasm types.
    - `sizing.ml`: Functions for taking the sizes of types.
    - `solver.ml`: A solver for determining whether relationships between different quals/sizes are provable from a set of assumptions. Many RichWasm typing rules require chekcing relationships of the form "given the relationships between many abstract and concrete sizes, can it be proved that the size of a particular type is less than or equal to the size of a particular slot?"
    - `typing_defs.ml`: Definitions for different structures needed to typecheck RichWasm, including local contexts, function contexts, and store typings, as well as their associated functions
    - `rich_wasm_typechecker.ml`: A typechecker for RichWasm, as well as a function which transforms RichWasm into annotated RichWasm.
    - `typechecking_tests.ml`: Tests for the typechecker and annotator at the top-level (there are tests of other properties in other files).
- `richwasm/`: Compiler from RichWasm to WebAssembly.
    - `src/`: Rust Source code of the compiler.
        - `allocator.wasm`: Allocator used in WebAssembly files being generated by the compiler.  
        - `main.rs`: CLI for the compiler.
        - `parse.rs`: Parser for annotated RichWasm code. 
        - `parse_tests.rs`: Hand written tests for the parser.
        - `rwasm.rs`: Data structure for RichWasm code. 
        - `translate_insts.rs`: Instruction specific translation code.
        - `translate.rs`: Tranlation of modules, tables, etc. 
        - `translate_tests.rs`: Translation tests for different groups of instructions, with expected outputs. 
    - `tests/`: Parser and translation tests for the compiler 
        - `parser/`: Some parser tests
        -  `translation_tests/`: RichWasm code along with expected outputs.       

- `source_examples/`: Source ML and L3 examples.
    - Each subdirectory contains source examples. Running the following commands from within a subdirectory will compile them to RichWasm and verify that they typecheck (note that if the directory name contains "fail" then it is meant to fail to typecheck, as RichWasm catches an interop error):
```
../../_build/default/ml/rich_wasm_of_ml.exe -i . -o .
../../_build/default/l3/rich_wasm_of_l3.exe -i . -o .
../../_build/default/rich_wasm/annotated_rich_wasm_of_rich_wasm.exe -i . -o . -just-typecheck
```


## Extending the Artifact

Any researchers or developers looking to compile to RichWasm, use it, or extend it may benefit from this artifact. 
This artifact contains the extensive proof of RichWasm's type safety which will be used to extend the language in the future, as detailed in Section 8. 
Researchers looking to compile to RichWasm have two source compilers with different source type systems to inspect and study. Additionally, we have included examples of interoperation between ML and L3 for examples of fine-grained sharing between two languages with GC'd memory and manually managed memory. This would be useful for researchers thinking about different types of interoperation.
The RichWasm to WebAssembly compiler has also been written with extensibility in mind, since we plan on extending RichWasm in the future so that it can make use of newer WebAssembly features and support type preserving compilers from languages like Rust. 

## Running Locally

If you want to run our analyses and evaluation yourself, here is a rough list of the required software and input data:

- OS: Ubuntu 22.04 LTS
- OCaml compiler versions 5.0.0 and 4.08.1, see https://ocaml.org/
- Coq version 8.13.2, see https://coq.inria.fr/
- Rust distribution > version 1.60 (rustc, cargo, etc.), see https://rustup.rs/
- Wasmtime as a WASI-compliant WebAssembly VM, see https://github.com/bytecodealliance/wasmtime
