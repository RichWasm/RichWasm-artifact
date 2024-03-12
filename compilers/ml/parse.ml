open! Core
open! Syntax
open Angstrom
open! Let_syntax

let illegal_identifiers =
  [ "Int"
  ; "Unit"
  ; "Ref"
  ; "Rec"
  ; "if0"
  ; "then"
  ; "else"
  ; "let"
  ; "in"
  ; "fun"
  ; "new"
  ; "new_lin"
  ; "inj"
  ; "case"
  ; "proj"
  ; "fold"
  ; "unfold"
  ; "import"
  ; "export"
  ]
;;

let whitespace = skip_while Char.is_whitespace
let required_whitespace = take_while1 Char.is_whitespace >>| Fn.const ()
let number = take_while1 Char.is_digit >>| int_of_string
let name = take_while1 (fun c -> Char.(is_alphanum c || c = '_'))

let identifier =
  name
  >>= fun s ->
  match List.find illegal_identifiers ~f:(String.equal s) with
  | Some s -> fail [%string "Illegal identifier %{s}"]
  | None -> return s
;;

let list_ () = sep_by (char ',' *> whitespace)
let list_semi () = sep_by (char ';' *> whitespace)

let pattern_binding =
  let open Source.Pattern_binding in
  let unit_ =
    let+ _ = string "()" in
    Unit
  in
  let name =
    let+ name = identifier in
    Variable name
  in
  let tuple =
    let+ names =
      char '(' *> whitespace *> list_ () identifier <* whitespace <* char ')'
    in
    Tuple names
  in
  whitespace *> choice ~failure_msg:"could not determine pattern" [ unit_; name; tuple ]
  <* whitespace
;;

module Type = struct
  open Source.Pretype
  open Source.Funtype
  open Source.Type

  let unit_ =
    let+ _ = string "Unit" in
    Unit
  ;;

  let int_ =
    let+ _ = string "Int" in
    Int
  ;;

  let var =
    let+ s = identifier in
    Var s
  ;;

  let type_ =
    fix (fun type_ ->
      let fun_ =
        let+ foralls =
          string "(A" *> whitespace *> char '[' *> whitespace *> list_ () identifier
          <* whitespace
          <* char ']'
          <* whitespace
          <* char '.'
          <* whitespace
        and+ args = list_ () type_ <* string "->" <* whitespace
        and+ ret = type_ <* whitespace <* char ')' in
        Fun { foralls; args; ret }
      in
      let ref_ =
        let+ typ = string "Ref" *> whitespace *> type_ in
        Ref typ
      in
      let variant =
        let+ ts =
          char '(' *> required_whitespace *> char '+' *> list_ () type_ <* char ')'
        in
        Variant ts
      in
      let prod =
        let+ ts =
          char '(' *> required_whitespace *> char '*' *> list_ () type_ <* char ')'
        in
        Prod ts
      in
      let rec_ =
        let+ var = string "Rec" *> whitespace *> identifier <* whitespace <* char '.'
        and+ t = whitespace *> type_ in
        Rec (var, t)
      in
      let pretype_ =
        whitespace
        *> choice
             ~failure_msg:"could not determine pretype"
             [ int_; unit_; var; fun_; ref_; variant; prod; rec_ ]
        <* whitespace
      in
      let unr =
        let+ pt = pretype_ in
        Typ pt
      in
      let lin =
        let+ pt = char '<' *> pretype_ <* char '>' in
        Lin pt
      in
      whitespace *> choice ~failure_msg:"could not determine type" [ unr; lin ]
      <* whitespace)
  ;;

  let parse_type s =
    match parse_string ~consume:All type_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_type |> sexp_of_t |> print_s

  let%expect_test "parse type" =
    f
      "( * <Int>, Unit, asdf, (A [a1,a2] . <Ref < a1 >>, Rec a3. a3, ( + Unit, a2) -> \
       Int))";
    [%expect
      {|
      (Typ
       (Prod
        ((Lin Int) (Typ Unit) (Typ (Var asdf))
         (Typ
          (Fun
           ((foralls (a1 a2))
            (args
             ((Lin (Ref (Lin (Var a1)))) (Typ (Rec a3 (Typ (Var a3))))
              (Typ (Variant ((Typ Unit) (Typ (Var a2)))))))
            (ret (Typ Int)))))))) |}]
  ;;
end

module Expr = struct
  open Source.Expr

  let int_ =
    let+ f = option Fn.id (char '-' |> map ~f:(fun _ -> Int.neg))
    and+ i = number in
    Int (f i)
  ;;

  let unit_ =
    let+ _ = string "()" in
    Unit
  ;;

  let var =
    let+ s = identifier in
    Var s
  ;;

  let expr_ =
    fix (fun expr_ ->
      let binop =
        let+ op =
          char '('
          *> required_whitespace
          *> choice [ char '+'; char '-'; char '*'; char '/' ]
        and+ t1 = expr_
        and+ t2 = expr_ <* char ')' in
        let op =
          match op with
          | '+' -> `Add
          | '-' -> `Sub
          | '*' -> `Mul
          | '/' -> `Div
          | _ ->
            raise_s [%message "BUG: Internal compiler invariant violated: binop parsing"]
        in
        Binop (t1, t2, op)
      in
      let if0 =
        let+ cond = string "if0" *> required_whitespace *> expr_
        and+ then_ = string "then" *> expr_
        and+ else_ = string "else" *> expr_ in
        If0 (cond, then_, else_)
      in
      let let_ =
        let+ var =
          string "let" *> required_whitespace *> pattern_binding <* whitespace <* char '='
        and+ bind = expr_
        and+ body = string "in" *> expr_ in
        Let { var; bind; body }
      in
      let lambda =
        let+ foralls =
          string "fun"
          *> required_whitespace
          *> char '['
          *> whitespace
          *> list_ () identifier
          <* whitespace
          <* char ']'
          <* whitespace
          <* char '.'
        and+ args =
          whitespace
          *> list_ () (both (pattern_binding <* whitespace <* char ':') Type.type_)
          <* string "->"
        and+ body = expr_ in
        Lambda { foralls; args; body }
      in
      let apply =
        let+ f = char '(' *> expr_
        and+ inst = char '[' *> list_ () Type.type_ <* char ']' <* whitespace
        and+ args = char '(' *> list_ () expr_ <* char ')' <* whitespace <* char ')' in
        Apply { inst; f; args }
      in
      let new_ =
        let+ t = string "new" *> required_whitespace *> expr_ in
        New t
      in
      let new_lin =
        let+ type_ = string "new_lin" *> required_whitespace *> Type.type_ in
        New_lin type_
      in
      let deref =
        let+ t = char '!' *> expr_ in
        Deref t
      in
      let assign =
        let+ ref = char '(' *> expr_ <* string ":="
        and+ value = expr_ <* char ')' in
        Assign { ref; value }
      in
      let inj =
        let+ n = string "inj" *> required_whitespace *> number
        and+ typ =
          whitespace *> char '(' *> required_whitespace *> char '+' *> list_ () Type.type_
          <* char ')'
        and+ value = expr_ in
        Inj { n; typ; value }
      in
      let case =
        let+ var =
          string "case" *> required_whitespace *> identifier <* whitespace <* char '='
        and+ bind = expr_ <* string "in" <* whitespace
        and+ body = char '{' *> list_semi () expr_ <* char '}' in
        Case { var; bind; body }
      in
      let prod =
        let+ ts =
          char '(' *> required_whitespace *> char '*' *> list_ () expr_ <* char ')'
        in
        Prod ts
      in
      let proj =
        let+ n = string "proj" *> required_whitespace *> number
        and+ e = expr_ in
        Proj { e; n }
      in
      let fold =
        let+ e = string "fold" *> required_whitespace *> expr_
        and+ typ = string "as" *> Type.type_ in
        Fold { typ; e }
      in
      let unfold =
        let+ e = string "unfold" *> required_whitespace *> expr_ in
        Unfold e
      in
      whitespace
      *> choice
           ~failure_msg:"could not parse expr"
           [ int_
           ; binop
           ; if0
           ; let_
           ; var
           ; unit_
           ; lambda
           ; apply
           ; new_lin
           ; new_
           ; deref
           ; assign
           ; inj
           ; case
           ; prod
           ; proj
           ; fold
           ; unfold
           ]
      <* whitespace)
  ;;

  let parse_expr s =
    match parse_string ~consume:All expr_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_expr |> sexp_of_t |> print_s

  let%expect_test "parse expr" =
    f
      {|
let a = 3 in
let b = () in
let c = if0 ( + a 3) then ( / a 3) else ( - a a) in
let d = fun [] . -> () in
let d = fun [a1,a2] . x : Int, y : ( * Unit, Int ) -> x in
let e = (d [Int, Unit] (3, b)) in
let f = new 2 in
let g = !f in
let h = (f := 5) in
let i = inj 0 ( + Unit, Int) () in
let j = case x = i in {x; ( + x 1)} in
let k = ( * 3, (), new ()) in
let l = proj 2 k in
let m = fold () as Unit in
let n = unfold m in
let o = new_lin <Int> in
let (p, q) = ( * 1, 2) in
let r = fun []. (x, y) : ( * Int, Int), () : Unit -> () in
()
      |};
    let (_ : string) = {|

     |} in
    [%expect
      {|
      (Let (var (Variable a)) (bind (Int 3))
       (body
        (Let (var (Variable b)) (bind Unit)
         (body
          (Let (var (Variable c))
           (bind
            (If0 (Binop (Var a) (Int 3) Add) (Binop (Var a) (Int 3) Div)
             (Binop (Var a) (Var a) Sub)))
           (body
            (Let (var (Variable d)) (bind (Lambda (args ()) (body Unit)))
             (body
              (Let (var (Variable d))
               (bind
                (Lambda (foralls (a1 a2))
                 (args
                  (((Variable x) (Typ Int))
                   ((Variable y) (Typ (Prod ((Typ Unit) (Typ Int)))))))
                 (body (Var x))))
               (body
                (Let (var (Variable e))
                 (bind
                  (Apply (f (Var d)) (inst ((Typ Int) (Typ Unit)))
                   (args ((Int 3) (Var b)))))
                 (body
                  (Let (var (Variable f)) (bind (New (Int 2)))
                   (body
                    (Let (var (Variable g)) (bind (Deref (Var f)))
                     (body
                      (Let (var (Variable h))
                       (bind (Assign (ref (Var f)) (value (Int 5))))
                       (body
                        (Let (var (Variable i))
                         (bind
                          (Inj (n 0) (typ ((Typ Unit) (Typ Int))) (value Unit)))
                         (body
                          (Let (var (Variable j))
                           (bind
                            (Case (var x) (bind (Var i))
                             (body ((Var x) (Binop (Var x) (Int 1) Add)))))
                           (body
                            (Let (var (Variable k))
                             (bind (Prod ((Int 3) Unit (New Unit))))
                             (body
                              (Let (var (Variable l))
                               (bind (Proj (e (Var k)) (n 2)))
                               (body
                                (Let (var (Variable m))
                                 (bind (Fold (typ (Typ Unit)) (e Unit)))
                                 (body
                                  (Let (var (Variable n)) (bind (Unfold (Var m)))
                                   (body
                                    (Let (var (Variable o))
                                     (bind (New_lin (Lin Int)))
                                     (body
                                      (Let (var (Tuple (p q)))
                                       (bind (Prod ((Int 1) (Int 2))))
                                       (body
                                        (Let (var (Variable r))
                                         (bind
                                          (Lambda
                                           (args
                                            (((Tuple (x y))
                                              (Typ (Prod ((Typ Int) (Typ Int)))))
                                             (Unit (Typ Unit))))
                                           (body Unit)))
                                         (body Unit)))))))))))))))))))))))))))))))))))) |}]
  ;;
end

module Module = struct
  open Source.Module

  let module_ =
    fix (fun module_ ->
      let funtype =
        let+ foralls =
          string "(A" *> whitespace *> char '[' *> whitespace *> list_ () identifier
          <* whitespace
          <* char ']'
          <* whitespace
          <* char '.'
          <* whitespace
        and+ args = list_ () Type.type_ <* string "->" <* whitespace
        and+ ret = Type.type_ <* whitespace <* char ')' in
        Source.Funtype.{ foralls; args; ret }
      in
      let import =
        let+ mod_name = string "import" *> whitespace *> identifier <* char '.'
        and+ fun_name = identifier <* whitespace <* char ':'
        and+ typ = whitespace *> funtype <* whitespace <* string "in"
        and+ m = module_ in
        LetIm ({ typ; mod_name; fun_name }, m)
      in
      let func =
        let+ foralls =
          string "fun" *> whitespace *> char '[' *> whitespace *> list_ () identifier
          <* whitespace
          <* char ']'
          <* whitespace
          <* char '.'
        and+ args =
          whitespace
          *> list_ () (both (pattern_binding <* whitespace <* char ':') Type.type_)
          <* string "->"
        and+ body = Expr.expr_ in
        { foralls; args; body }
      in
      let export =
        let+ ex_name =
          string "export" *> whitespace *> identifier
          <* whitespace
          <* char '='
          <* whitespace
        and+ func = func <* string "in"
        and+ m = module_ in
        LetEx (ex_name, func, m)
      in
      let global =
        let+ glob_name =
          string "global" *> whitespace *> identifier
          <* whitespace
          <* char '='
          <* whitespace
        and+ glob_binding = Expr.expr_ <* string "in"
        and+ m = module_ in
        Global (glob_name, glob_binding, m)
      in
      let body =
        let+ e = Expr.expr_ in
        Body e
      in
      whitespace
      *> choice
           ~failure_msg:"could not parse module"
           [ import <?> "import"
           ; export <?> "export"
           ; global <?> "global"
           ; body <?> "body"
           ]
      <* whitespace)
  ;;

  let parse_module s =
    match parse_string ~consume:All module_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_module |> sexp_of_t |> print_s

  let%expect_test "parse module" =
    f
      {| 
import ML_module.example_function1 : (A []. <Int>, Unit -> Unit) in
import L3_module.example_function2 : (A []. <Unit>, Int -> Int) in
global r = new 3 in
export f = fun [a]. x : <a> -> x in
()
      |};
    [%expect
      {|
      (LetIm
       ((typ ((foralls ()) (args ((Lin Int) (Typ Unit))) (ret (Typ Unit))))
        (mod_name ML_module) (fun_name example_function1))
       (LetIm
        ((typ ((foralls ()) (args ((Lin Unit) (Typ Int))) (ret (Typ Int))))
         (mod_name L3_module) (fun_name example_function2))
        (Global r (New (Int 3))
         (LetEx f
          ((foralls (a)) (args (((Variable x) (Lin (Var a))))) (body (Var x)))
          (Body Unit))))) |}]
  ;;
end

let parse = Module.parse_module

(*
   https://arthursonzogni.com/Diagon/#Grammar
{|
pretype = "Unit"
        | "Int"
        | identifier
        | "(A" "[" { identifier {"," identifier} } "]" "." {type {"," type}} "->" type ")"
        | "Ref" type
        | "( +" {type {"," type}} ")"
        | "( *" {type {"," type}} ")"
        | "Rec" identifier "." type
        | "Lin" 
.

type = pretype | "<" pretype ">" .

binding = "()"
        | identifier
        | "(" identifier {"," identifier } ")"
.

typed_binding = binding ":" type .

binop = "+" | "-" | "*" | "/" .

expr = "()"
     | integer
     | identifier
     | "( " binop expr expr ")"
     | "if0" expr "then" expr "else" expr
     | "let" binding "=" expr "in" expr
     | "fun" "[" {identifier {"," identifier}} "]" "." { typed_binding { "," typed_binding} } "->" expr
     | "(" expr "[" {type {"," type}} "]" "(" {expr {"," expr}} ")" ")"
     | "new" expr
     | "new_lin" type
     | "!" expr
     | "(" expr ":=" expr ")"
     | "inj" natrual "( +" {type {"," type}} ")" expr
     | "case" identifier "=" expr "in" "{" {expr {";" expr}} "}"
     | "( *" {expr {"," expr}} ")"
     | "proj" natural expr
     | "fold" expr "as" type
     | "unfold" expr
.

module = "import" identifier "." identifier ":" "(A" "[" { identifier {"," identifier} } "]" "." {type {"," type}} "->" type ")" "in" module
       | "export" identifier "=" "fun" "[" {identifier {"," identifier}} "]" "." { typed_binding { "," typed_binding} } "->" expr "in" module
       | "global" identifier "=" expr "in" module
       | expr
.
|}
*)
