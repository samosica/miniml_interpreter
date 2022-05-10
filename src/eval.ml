open Syntax 

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値．今回
   の言語ではこの両者は同じになるが，この2つが異なる言語もある．教科書
   参照． *)
type exval =
  | IntV of int
  | BoolV of bool
  | ListV of exval list
  | ProcV of id * exp * dnval Environment.t ref
  | VariV of id * exval list
  | LocV of int
  | UnitV
and dnval = exval

exception Error of string
exception Internal_Match_Failure
                 
let err s = raise (Error s)

let store = Store.make()

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | ListV [] -> "[]"
  | ListV (v1::l) -> "[" ^ string_of_exval v1
                     ^ List.fold_right (fun v acc -> "; " ^ string_of_exval v ^ acc) l ""
                     ^ "]"
  | ProcV _ -> "<fun>"
  | VariV (id, vs) ->
     (match vs with
        [] -> id
      | [VariV (_, _ :: _) as v] -> id ^ " (" ^ string_of_exval v ^ ")"
      | [v] -> id ^ " " ^ string_of_exval v
      | v :: vs -> id ^ " (" ^ string_of_exval v ^ List.fold_right (fun v acc -> ", " ^ string_of_exval v ^ acc) vs "" ^ ")")
  | LocV l -> "{contents = " ^ string_of_exval (Store.lookup l store) ^ "}"
  | UnitV -> "()"
             
let pp_val v = print_string (string_of_exval v)
             
let apply_prim op arg1 arg2 = match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")
  | Append, e, ListV l -> ListV (e :: l)
  | Append, _, _ -> err ("2nd argument must be list: ::")
  | LAnd, IntV i1, IntV i2 -> IntV (i1 land i2)
  | LAnd, _, _ -> err ("Both arguments must be integer: land")
  | Lsr, IntV i1, IntV i2 -> IntV (i1 lsr i2)
  | Lsr, _, _ -> err ("Both arguments must be integer: lsr")
  | Mod, IntV i1, IntV i2 -> IntV (i1 mod i2)
  | Mod, _, _ -> err ("Both arguments must be integer: mod")
  | _, _, _ -> err ""
             
let intersect s1 s2 = List.fold_right
                        (fun x l -> if List.mem x s2
                                    then x :: l
                                    else l) s1 [] ;;

(* compatible with List.assoc_opt *)
let assoc_opt x l =
  try
    Some (List.assoc x l)
  with
    Not_found -> None

let rec eval_exp env exp =
  match exp.exp_desc with
    Var x -> 
      (try Environment.lookup x env with 
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | EmptyList -> ListV []
  | BinOp (And, exp1, exp2) ->
     let arg1 = eval_exp env exp1 in
     (match arg1 with
        BoolV false -> BoolV false
      | BoolV true ->
         let arg2 = eval_exp env exp2 in
         (match arg2 with
            BoolV _ -> arg2
          | _ -> err ("Both arguments must be bool: &&"))
      | _ -> err ("1st argument must be bool: &&"))
  | BinOp (Or, exp1, exp2) ->
     let arg1 = eval_exp env exp1 in
     (match arg1 with
        BoolV true -> BoolV true
      | BoolV false ->
         let arg2 = eval_exp env exp2 in
         (match arg2 with
            BoolV _ -> arg2
          | _ -> err ("Both arguments must be bool: ||"))
      | _ -> err ("1st argument must be bool: ||"))   
  | BinOp (op, exp1, exp2) -> 
      let arg1 = eval_exp env exp1 in
      let arg2 = eval_exp env exp2 in
      apply_prim op arg1 arg2
  | IfExp (exp1, exp2, exp3) ->
      let test = eval_exp env exp1 in
        (match test with
            BoolV true -> eval_exp env exp2 
          | BoolV false -> eval_exp env exp3
          | _ -> err ("Test expression must be boolean: if"))
  | LetExp (ps, exp) -> (* declare simultaneously *)
     let newenv = List.fold_left (fun newenv (id, _, e) ->
                      let v = eval_exp env e in
                      Environment.extend id v newenv
                    ) env ps in
     eval_exp newenv exp
  | LetRecExp (ts, exp) -> (* declare simultaneously *)
     let dummyenv = ref Environment.empty in
     let newenv =
       List.fold_left (fun newenv (id, _, para, body) ->
           Environment.extend id (ProcV (para, body, dummyenv)) newenv) env ts in
     dummyenv := newenv;
     eval_exp newenv exp
  | FunExp (param, exp) ->
     let id = match param with
         Param id -> id
       | TypedParam (id, _, _) -> id in
     ProcV (id, exp, ref env)
  | AppExp (exp1, exp2) ->
     let funval = eval_exp env exp1 in
     let arg = eval_exp env exp2 in
     (match funval with
        ProcV (id, body, env') ->
         let newenv = Environment.extend id arg !env' in
         eval_exp newenv body
      | _ -> err ("Non-function value is applied"))
  | MatchExp (exp, pm) ->
     let v = eval_exp env exp in
     let rec go = function
         [] -> raise (Failure "Matching failure")
       | (p, e) :: rest ->
          try
            let bs = pattern_match v p in
            let newenv = List.fold_left (fun env (x, e) -> Environment.extend x e env) env bs in
            eval_exp newenv e
          with
            Internal_Match_Failure -> go rest in
     go pm
  | TypedExp (exp, _) -> eval_exp env exp
  | VariExp (id, es) ->
     VariV (id, List.map (eval_exp env) es)
  | RefExp exp ->
     let v = eval_exp env exp in
     LocV (Store.allocate v store)
  | AssnExp (exp1, exp2) ->
     let v1 = eval_exp env exp1 in
     let v2 = eval_exp env exp2 in
     (match v1 with
        LocV l -> Store.update l v2 store; UnitV
      | _ -> err "Left operand must be reference: :=")
  | DerefExp exp ->
     let v = eval_exp env exp in
     (match v with
        LocV l -> Store.lookup l store
      | _ -> err "Operand must be reference: !")
  | UnitExp -> UnitV
     
and pattern_match v p =
  match v, p.Pattern.pat_desc with
    _, Pattern.Var x -> [(x, v)]
  | _, Pattern.Ignore -> []
  | IntV v, Pattern.ILit w when v = w -> []
  | BoolV v, Pattern.BLit w when v = w -> []
  | ListV [], Pattern.EmptyList -> []
  | _, Pattern.Or (p1, p2) ->
     (try
        pattern_match v p1
      with
        Internal_Match_Failure -> pattern_match v p2)
  | ListV (v1 :: l), Pattern.Append (p1, p2) ->
     let bs = pattern_match v1 p1 in
     let bs' = pattern_match (ListV l) p2 in
     (match intersect (List.map (fun (x, _) -> x) bs) (List.map (fun (x, _) -> x) bs') with
       [] -> bs @ bs'
     | x :: _ -> raise (Failure ("Variable " ^ x ^ " is bound several times in this matching")))
  | VariV (id, vs), Pattern.Vari (id', ps) when id = id' ->
     List.fold_left2 (fun bs v p -> (pattern_match v p) @ bs) [] vs ps
  | UnitV, Pattern.Unit -> []
  | _, _ -> raise Internal_Match_Failure
     
let rec eval_decl env tydef = function
    Exp e -> let v = eval_exp env e in ([("-", v)], env)
  | Decl ps ->
     let ps = List.fold_right (fun (id, _, e) ps ->
                  let v = eval_exp env e in
                  match assoc_opt id ps with
                    Some _ -> err ("Variable " ^ id ^ " is bound several times in this declaration")
                  | None -> (id, v) :: ps) ps [] in
     let newenv = List.fold_left (fun env (id, v) -> Environment.extend id v env) env ps in
     (ps, newenv)
  | RecDecl ts ->
     let _ = List.fold_left (fun qs (id, _, _, _) ->
                 if List.mem id qs
                 then err ("Variable " ^ id ^ " is bound several times in this declaration")
                 else id :: qs) [] ts in
     let dummyenv = ref Environment.empty in
     let ps = List.fold_right (fun (id, _, para, body) acc ->
                  (id, ProcV (para, body, dummyenv)) :: acc
                ) ts [] in
     let newenv = List.fold_left (fun env (id, v) -> Environment.extend id v env) env ps in
     dummyenv := newenv;
     (ps, newenv)
  | Seq progs ->
     let (bs, newenv) = List.fold_left (fun (bs, env) d ->
                            let (cs, env') = eval_decl env tydef d in
                            (bs @ cs, env')) ([], env) progs in
     (bs, newenv)
  | TyDef _ -> ([], env)
     
