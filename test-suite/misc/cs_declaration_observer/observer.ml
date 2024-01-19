
let o = open_out "main.out"

let observe env sigma lhs rhs =
   Printf.fprintf o "chaine"; None

let () = Evarconv.register_hook ~name:"test observer" observe

let () = Evarconv.activate_hook ~name:"test observer"
