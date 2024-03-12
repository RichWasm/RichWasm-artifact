global l = new fold inj 0 ( + Unit, ( * Ref <Ref Int>, Rec l. ( + Unit, ( * Ref <Ref Int>, l)))) () as Rec l. ( + Unit, ( * Ref <Ref Int>, l)) in
export cons = fun [x]. l : Rec l. ( + Unit, ( * x, l)), x : x ->
  fold inj 1 ( + Unit, ( * x, Rec l. ( + Unit, ( * x, l)))) ( * x, l)  as Rec l. ( + Unit, ( * x, l))
in
export stash = fun []. i : <Ref Int> ->
  let r = new_lin <Ref Int> in
  let () = (r := i) in
  (l := (cons [Ref <Ref Int>] (!l, r)))
in
export unstash = fun []. ->
  case l_ = unfold !l in
  { let empty = new_lin <Ref Int> in !empty
  ; let () = (l := proj 1 l_) in
    let top = proj 0 l_ in
    !top
  }
in
()
