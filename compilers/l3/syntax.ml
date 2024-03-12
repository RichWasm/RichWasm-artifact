open Core

module Tag = struct
  type t = int [@@deriving sexp, equal]

  let new_counter () : unit -> t =
    let x = ref 0 in
    fun () ->
      let y = !x in
      x := y + 1;
      y
  ;;
end

module Nativity = struct
  type t =
    | Native
    | Foreign
  [@@deriving sexp]
end

module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module Binding = struct
    type t = string [@@deriving sexp]
  end

  module Binding_or_unit = struct
    type t =
      [ `Binding of string
      | `Unit
      ]
    [@@deriving sexp]
  end

  module Type = struct
    type t =
      | Int
      | Unit
      | Prod of t list
      | Fun of
          { foralls : Binding.t list
          ; args : t list
          ; ret : t
          }
      | Bang of t
      | Ptr of Variable.t
      | Cap of Variable.t * t * int
      | Ref of Variable.t * t * int * Nativity.t
      | Exists of Binding.t * t
    [@@deriving sexp]
  end

  module Expr = struct
    type t =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | Unit
      | LetUnit of
          { bind : t
          ; body : t
          }
      | Prod of t list
      | LetProd of
          { vars : Binding_or_unit.t list
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Apply of
          { f : t
          ; args : t list
          }
      | Bang of t
      | LetBang of
          { var : Binding_or_unit.t
          ; bind : t
          ; body : t
          }
      | Dupl of t
      | Drop of t
      | New of t * int
      | Free of t
      | Swap of t * t
      | Join of t
      | Split of t
      | Inst of t * Variable.t list
      | Pack of Variable.t * t
      | Unpack of
          { locvar : Binding.t
          ; var : Binding_or_unit.t
          ; package : t
          ; body : t
          }
    [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Type.t
      ; mod_name : Variable.t
      ; fun_name : Binding.t
      }
    [@@deriving sexp]

    type func =
      { foralls : Binding.t list
      ; args : (Binding_or_unit.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of Binding.t * func * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Tagged = struct
  module Variable = Source.Variable
  module Binding = Source.Binding
  module Binding_or_unit = Source.Binding_or_unit

  module Type = struct
    type t_base =
      | Int
      | Unit
      | Prod of t list
      | Fun of
          { foralls : Binding.t list
          ; args : t list
          ; ret : t
          }
      | Bang of t
      | Ptr of Variable.t
      | Cap of Variable.t * t * int
      | Ref of Variable.t * t * int * Nativity.t
      | Exists of Binding.t * t
    [@@deriving sexp]

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | Unit
      | LetUnit of
          { bind : t
          ; body : t
          }
      | Prod of t list
      | LetProd of
          { vars : Binding_or_unit.t list
          ; bind : t
          ; body : t
          }
      | Var of string
      | Apply of
          { f : t
          ; args : t list
          }
      | Bang of t
      | LetBang of
          { var : Binding_or_unit.t
          ; bind : t
          ; body : t
          }
      | Dupl of t
      | Drop of t
      | New of t * int
      | Free of t
      | Swap of t * t
      | Join of t
      | Split of t
      | Inst of t * Variable.t list
      | Pack of Variable.t * t
      | Unpack of
          { locvar : Binding.t
          ; var : Binding_or_unit.t
          ; package : t
          ; body : t
          }
    [@@deriving sexp]

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Type.t
      ; mod_name : Variable.t
      ; fun_name : Binding.t
      }
    [@@deriving sexp]

    type func =
      { foralls : Binding.t list
      ; args : (Binding_or_unit.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of string * func * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Debruijned = struct
  module Variable = struct
    type t = int [@@deriving sexp]
  end

  module Binding_or_unit = struct
    type t =
      [ `Binding
      | `Unit
      ]
    [@@deriving sexp]
  end

  module Type = struct
    type t_base =
      | Int
      | Unit
      | Prod of t list
      | Fun of
          { foralls : int
          ; args : t list
          ; ret : t
          }
      | Bang of t
      | Ptr of Variable.t
      | Cap of Variable.t * t * int
      | Ref of Variable.t * t * int * Nativity.t
      | Exists of t
    [@@deriving sexp]

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | Unit
      | LetUnit of
          { bind : t
          ; body : t
          }
      | Prod of t list
      | LetProd of
          { vars : Binding_or_unit.t list
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Fun of int
      | Apply of
          { f : t
          ; args : t list
          }
      | Bang of t
      | LetBang of
          { var : Binding_or_unit.t
          ; bind : t
          ; body : t
          }
      | Dupl of t
      | Drop of t
      | New of t * int
      | Free of t
      | Swap of t * t
      | Join of t
      | Split of t
      | Inst of t * Variable.t list
      | Pack of Variable.t * t
      | Unpack of
          { var : Binding_or_unit.t
          ; package : t
          ; body : t
          }
    [@@deriving sexp]

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Type.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : int
      ; args : (Binding_or_unit.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of string * func * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Typechecked = struct
  module Variable = Debruijned.Variable
  module Binding_or_unit = Debruijned.Binding_or_unit
  module Type = Debruijned.Type

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | Unit
      | LetUnit of
          { bind : t
          ; body : t
          }
      | Prod of t list
      | LetProd of
          { vars : Binding_or_unit.t list
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Fun of int
      | Apply of
          { f : t
          ; args : t list
          }
      | Bang of t
      | LetBang of
          { var : Binding_or_unit.t
          ; bind : t
          ; body : t
          }
      | Dupl of t
      | Drop of t
      | New of t * int
      | Free of t
      | Swap of t * t
      | Join of t
      | Split of t
      | Inst of t * Variable.t list
      | Pack of Variable.t * t
      | Unpack of
          { var : Binding_or_unit.t
          ; package : t
          ; body : t
          }
    [@@deriving sexp]

    and t =
      | Info of
          { tag : Tag.t
          ; typ : Type.t
          ; e : t_base
          }
    [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Type.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : int
      ; args : (Binding_or_unit.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of string * func * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end
