global r = new_lin <Ref Int> in
export stash = fun []. l : <Ref Int> ->
  let () = (r := l) in
  l
in
export get_stashed = fun []. -> !r in
()
