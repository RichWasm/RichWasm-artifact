global r = new_lin <Ref Int> in
export stash = fun []. l : <Ref Int> ->
  let () = (r := l) in ()
in
export get_stashed = fun []. () : Unit ->
  !r
in
()
