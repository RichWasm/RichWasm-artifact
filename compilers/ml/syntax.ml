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

module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module Binding = struct
    type t = string [@@deriving sexp]
  end

  module Pattern_binding = struct
    type t =
      | Unit
      | Variable of Binding.t
      | Tuple of Binding.t list
    [@@deriving sexp]
  end

  module rec Type : sig
    type t =
      | Lin of Pretype.t
      | Typ of Pretype.t
    [@@deriving sexp]
  end = struct
    type t =
      | Lin of Pretype.t
      | Typ of Pretype.t
    [@@deriving sexp]
  end

  and Pretype : sig
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Binding.t * Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Binding.t * Type.t
    [@@deriving sexp]
  end

  and Funtype : sig
    type t =
      { foralls : Binding.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end = struct
    type t =
      { foralls : Binding.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end

  module Expr = struct
    type t =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Unit
      | Lambda of
          { foralls : Binding.t list [@sexp.list]
          ; args : (Pattern_binding.t * Type.t) list
          ; body : t
          }
      | Apply of
          { f : t
          ; inst : Type.t list [@sexp.list]
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { var : Binding.t
          ; bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t
    [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Funtype.t
      ; mod_name : Variable.t
      ; fun_name : Binding.t
      }
    [@@deriving sexp]

    type func =
      { foralls : Binding.t list [@sexp.list]
      ; args : (Pattern_binding.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of Binding.t * func * t
      | Global of Binding.t * Expr.t * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Tagged = struct
  module Variable = Source.Variable
  module Binding = Source.Binding
  module Pattern_binding = Source.Pattern_binding

  module rec Type : sig
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end = struct
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  and Pretype : sig
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Binding.t * Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Binding.t * Type.t
    [@@deriving sexp]
  end

  and Funtype : sig
    type t =
      { foralls : Binding.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end = struct
    type t =
      { foralls : Binding.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Unit
      | Lambda of
          { foralls : Binding.t list [@sexp.list]
          ; args : (Pattern_binding.t * Type.t) list
          ; body : t
          }
      | Apply of
          { f : t
          ; inst : Type.t list [@sexp.list]
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { var : Binding.t
          ; bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Funtype.t
      ; mod_name : Variable.t
      ; fun_name : Binding.t
      }
    [@@deriving sexp]

    type func =
      { foralls : Binding.t list [@sexp.list]
      ; args : (Pattern_binding.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t * Tag.t
      | LetEx of Binding.t * func * t * Tag.t
      | Global of Binding.t * Expr.t * t * Tag.t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Debruijned = struct
  module Variable = struct
    type t = int [@@deriving sexp]
  end

  module Pattern_binding = struct
    type t =
      | Unit
      | Variable
      | Tuple of int
    [@@deriving sexp]
  end

  module rec Type : sig
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end = struct
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  and Pretype : sig
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Fun of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Type.t
    [@@deriving sexp]
  end

  and Funtype : sig
    type t =
      { foralls : int
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end = struct
    type t =
      { foralls : int
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Coderef of int
      | Global of int
      | Unit
      | Lambda of
          { foralls : int
          ; args : (Pattern_binding.t * Type.t) list
          ; body : t
          }
      | Apply of
          { f : t
          ; inst : Type.t list
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : Funtype.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : int
      ; args : (Pattern_binding.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t * Tag.t
      | LetEx of string * func * t * Tag.t
      | Global of Expr.t * t * Tag.t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Typechecked = struct
  module Variable = Debruijned.Variable
  module Pattern_binding = Debruijned.Pattern_binding
  module Type = Debruijned.Type
  module Pretype = Debruijned.Pretype
  module Funtype = Debruijned.Funtype

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Coderef of int
      | Global of int
      | Unit
      | Lambda of
          { foralls : int
          ; args : (Pattern_binding.t * Type.t) list
          ; body : t
          }
      | Apply of
          { f : t
          ; inst : Type.t list
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t

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
      { typ : Funtype.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : int
      ; args : (Pattern_binding.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t * Tag.t
      | LetEx of string * func * t * Tag.t
      | Global of Expr.t * t * Tag.t
      | Body of Expr.t
    [@@deriving sexp]
  end
end

module Hoisted = struct
  module Variable = Typechecked.Variable
  module Pattern_binding = Typechecked.Pattern_binding

  module rec Type : sig
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end = struct
    type t_base =
      | Lin of Pretype.t
      | Typ of Pretype.t

    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  and Pretype : sig
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Exists_closure of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Exists_closure of Funtype.t
      | Ref of Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Type.t
    [@@deriving sexp]
  end

  and Funtype : sig
    type t =
      { foralls : int
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end = struct
    type t =
      { foralls : int
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Coderef of
          { f : int
          ; env : t
          ; type_insts : Type.t list
          }
      | Global of int
      | Unit
      | Apply of
          { f : t
          ; inst : Type.t list
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t

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
      { typ : Funtype.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : int
      ; args : (Pattern_binding.t * Type.t) list
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t * Tag.t
      | LetEx of string * func * t * Tag.t
      | LetFun of func * t * Tag.t
      | Global of Expr.t * t * Tag.t
      | MainFun of func
    [@@deriving sexp]
  end
end

module Annotated = struct
  module Variable = Hoisted.Variable
  module Pattern_binding = Hoisted.Pattern_binding

  module Qual = struct
    type t =
      | Unr
      | Lin
    [@@deriving sexp, equal]
  end

  module Size = struct
    type t =
      | Const of int
      | Var of int
      | Plus of t * t
    [@@deriving sexp]
  end

  module Abstraction = struct
    type t =
      | Size
      | Type of Qual.t * Size.t
    [@@deriving sexp]
  end

  module rec Type : sig
    type t_base = Qual.t * Pretype.t
    and t = Info of Tag.t * t_base [@@deriving sexp]
  end = struct
    type t_base = Qual.t * Pretype.t
    and t = Info of Tag.t * t_base [@@deriving sexp]
  end

  and Pretype : sig
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Exists_closure of Funtype.t
      | Ref of Size.t * Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Qual.t * Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Unit
      | Exists_closure of Funtype.t
      | Ref of Size.t * Type.t
      | Variant of Type.t list
      | Prod of Type.t list
      | Rec of Qual.t * Type.t
    [@@deriving sexp]
  end

  and Funtype : sig
    type t =
      { foralls : Abstraction.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end = struct
    type t =
      { foralls : Abstraction.t list
      ; args : Type.t list
      ; ret : Type.t
      }
    [@@deriving sexp]
  end

  module Expr = struct
    type t_base =
      | Int of int
      | Binop of t * t * [ `Add | `Sub | `Mul | `Div ]
      | If0 of t * t * t
      | Let of
          { var : Pattern_binding.t
          ; bind : t
          ; body : t
          }
      | Var of Variable.t
      | Global of int
      | Unit
      | Coderef of
          { f : int
          ; env : t
          ; type_insts : Type.t list
          }
      | Apply of
          { f : t
          ; inst : (Size.t * Type.t) list
          ; args : t list
          }
      | New of t
      | New_lin of Type.t
      | Deref of t
      | Assign of
          { ref : t
          ; value : t
          }
      | Inj of
          { n : int
          ; typ : Type.t list
          ; value : t
          }
      | Case of
          { bind : t
          ; body : t list
          }
      | Prod of t list
      | Proj of
          { e : t
          ; n : int
          }
      | Fold of
          { typ : Type.t
          ; e : t
          }
      | Unfold of t

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
      { typ : Funtype.t
      ; mod_name : string
      ; fun_name : string
      }
    [@@deriving sexp]

    type func =
      { foralls : Abstraction.t list
      ; args : (Pattern_binding.t * Type.t) list
      ; ret : Type.t
      ; body : Expr.t
      }
    [@@deriving sexp]

    type t =
      | LetIm of import * t * Tag.t
      | LetEx of string * func * t * Tag.t
      | LetFun of func * t * Tag.t
      | Global of Expr.t * t * Tag.t
      | MainFun of func
    [@@deriving sexp]
  end
end
