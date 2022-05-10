open Syntax
open Eval
open Typing

let next_lexbuf = ref (fun () -> Lexing.from_channel stdin)
let is_interactive = ref true
                   
let rec read_eval_print env tydef tyenv =
  let input_lexbuf = !next_lexbuf () in
  let prompt = if !is_interactive then "# " else "" in
  print_string prompt;
  flush stdout;
  try
    let decl = Parser.toplevel Lexer.main input_lexbuf in
    let (newtyenv, newtydef, tys) = ty_decl tyenv tydef decl in
    let (ds, newenv) = eval_decl env newtydef decl in
    let ts = List.fold_right2 (fun (id, v) ty ts ->
                 match assoc_opt id ts with
                   Some _ -> ts
                 | None -> (id, (v, ty)) :: ts) ds tys [] in
    let () = match decl with (* TODO: 型定義を一度にいくつも書けるようにする *)
        TyDef tydef -> print_tydef tydef
      | _ -> () in
    List.iter (fun (id, (v, ty)) ->
        Printf.printf "val %s : " id;
        pp_ty ty;
        print_string " = ";
        pp_val v;
        print_newline()) ts;
    read_eval_print newenv newtydef newtyenv
  with
    Failure message ->
      print_endline message;
      read_eval_print env tydef tyenv
  | Parser.Error ->
      print_endline "Parse error";
      read_eval_print env tydef tyenv
  | Eval.Error message -> (* Syntax error *)
      print_endline message;
      read_eval_print env tydef tyenv
  | Typing.Error _ as err -> (* Type error *)
     Typing.print_error ~is_interactive:!is_interactive input_lexbuf err;
     read_eval_print env tydef tyenv
      
let interact env tydef tyenv = read_eval_print env tydef tyenv

let batch path env tydef tyenv =
  if not (Sys.file_exists path) then
    begin
      Printf.fprintf stderr "Cannot find file: %s\n" path;
      exit 1
    end;
  let relative_path =
    if Filename.is_implicit path
    then Filename.concat Filename.current_dir_name path
    else path in
  let ch = open_in path in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.Lexing.lex_curr_p <-
    { Lexing.pos_fname = relative_path
    ; Lexing.pos_lnum = 1
    ; Lexing.pos_cnum = 0
    ; Lexing.pos_bol = 0
    };  
  next_lexbuf := (fun () -> lexbuf);
  is_interactive := false;
  read_eval_print env tydef tyenv
  
let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10)
          (Environment.extend "ii" (IntV 2)
             (Environment.extend "iii" (IntV 3)
                (Environment.extend "iv" (IntV 4) Environment.empty)))))

let initial_tydef = 
  let di = [ ("C", ([], "t", []))
           ; ("D", ([TyInt], "t", []))
           ; ("E", ([TyInt; TyInt], "t", []))
           ; ("Cons", ([TyNamedVar "a"; TyVari ("mylist", [TyNamedVar "a"])], "mylist", [TyNamedVar "a"]))
           ; ("Nil", ([], "mylist", [TyNamedVar "a"]))
           ; ("Some", ([TyNamedVar "a"], "option", [TyNamedVar "a"]))
           ; ("None", ([], "option", [TyNamedVar "a"]))
           ] in
  List.fold_right (fun (cid, tu) env -> Environment.extend cid tu env) di Environment.empty

let initial_tyenv =
  Environment.extend "i" (tysc_of_ty TyInt)
    (Environment.extend "v" (tysc_of_ty TyInt)
       (Environment.extend "x" (tysc_of_ty TyInt)
          (Environment.extend "ii" (tysc_of_ty TyInt)
             (Environment.extend "iii" (tysc_of_ty TyInt)
                (Environment.extend "iv" (tysc_of_ty TyInt) Environment.empty)))))
  
let () =
  if Array.length Sys.argv < 2 then
    interact initial_env initial_tydef initial_tyenv
  else
    batch Sys.argv.(1) initial_env initial_tydef initial_tyenv
