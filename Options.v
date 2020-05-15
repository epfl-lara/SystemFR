Definition get_or_else { A } (opt: option A) (a: A) :=
  match opt with
  | None => a
  | Some x => x
  end.
