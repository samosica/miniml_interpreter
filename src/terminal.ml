let backup oc n =
  (* \027[nA: カーソルを n 行上に動かす
   * %!: flush
   *)
  Printf.fprintf oc "\027[%dA%!" n
    
(* b = true: the beginning of highlight
 * b = false: the end of highlight
 *)
let standout oc b =
  output_string oc (if b then "\027[4m" else "\027[0m"); flush oc
