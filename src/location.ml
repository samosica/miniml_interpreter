open Lexing

type t =
  {
    loc_start : position;
    loc_end   : position
  }

let dummy_loc = { loc_start = Lexing.dummy_pos
                ; loc_end = Lexing.dummy_pos
                }
  
let string_of_loc loc =
  "(" ^ string_of_int (loc.loc_start.pos_lnum)
  ^ ", " ^ string_of_int (loc.loc_start.pos_cnum)
  ^ ", " ^ string_of_int (loc.loc_start.pos_bol)
  ^ ")"
  ^ "--(" ^ string_of_int (loc.loc_end.pos_lnum)
  ^ ", " ^ string_of_int (loc.loc_end.pos_cnum)
  ^ ", " ^ string_of_int (loc.loc_end.pos_bol)
  ^ ")"

let highlight lexbuf locs =
  let num_lines = ref 0 in (* the number of lines of input *)
  for i = 0 to lexbuf.lex_buffer_len - 1 do
    let c = Bytes.get lexbuf.lex_buffer i in
    if c = '\n' then incr num_lines
  done;
  Terminal.backup stdout !num_lines;
  print_string "# "; (* prompt *)
  for i = 0 to lexbuf.lex_buffer_len - 1 do
    if List.exists (fun loc -> loc.loc_start.pos_cnum = i) locs
    then Terminal.standout stdout true;
    if List.exists (fun loc -> loc.loc_end.pos_cnum = i) locs
    then Terminal.standout stdout false;
    let c = Bytes.get lexbuf.lex_buffer i in
    print_char c
  done
