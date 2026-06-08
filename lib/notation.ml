let render_error notation frags =
  String.concat ""
    (List.map
       (function
         | Check.Text s -> s
         | Check.Term (names, t) -> Type.to_string_in ~notation names t)
       frags)
