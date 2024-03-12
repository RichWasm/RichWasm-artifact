open! Core
open! Syntax

val hoist : Typechecked.Module.t 
  -> source_printer:Source_printer.t
  -> Hoisted.Module.t Or_error.t
