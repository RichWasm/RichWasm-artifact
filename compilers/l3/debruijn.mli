open! Core
open! Syntax

val debruijn
  :  Tagged.Module.t
  -> source_printer:Source_printer.t
  -> Debruijned.Module.t Or_error.t
