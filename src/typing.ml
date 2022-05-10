open Syntax

type error =
  TypeError of { expected_ty : ty
               ; actual_ty : ty
               }
| TypeErrorPat of { expected_ty : ty
                  ; actual_ty : ty
                  }
| TypeErrorVar of { expected_ty : ty
                  ; actual_ty : ty
                  }
| UndefinedVariable of id
| DuplicateVariable of id
| UnmatchedVariablesInOrPattern of id
| NotFunction of { expected_ty : ty }
| NonFunctionApplied of { actual_ty : ty }
| UnmatchedParameterType of { expected_ty : ty
                            ; actual_ty : ty
                            }
| UndefinedConstructor of id
| UnmatchedConstructorArguments of { constr_name : string
                                   ; expected_num : int
                                   ; actual_num : int
                                   }
| DuplicateTypeParameter of ty

exception Error of Location.t * error
exception Unify

let err loc err = raise (Error (loc, err))

let print_error ~is_interactive lexbuf (Error (loc, err)) =
  if not is_interactive then
    (let pos = lexbuf.Lexing.lex_curr_p in
     let file_name = pos.Lexing.pos_fname in
     let line_num = loc.Location.loc_start.Lexing.pos_lnum in
     let col_start = loc.Location.loc_start.Lexing.pos_cnum - loc.Location.loc_start.Lexing.pos_bol in
     let col_end = loc.Location.loc_end.Lexing.pos_cnum - loc.Location.loc_start.Lexing.pos_bol in
     Printf.printf "File \"%s\", line %d, characters %d-%d:" file_name line_num col_start col_end;
     print_newline()
    );
  if is_interactive then Location.highlight lexbuf [loc];
  print_string "\027[91mError\027[0m: ";
  match err with
    TypeError d -> print_string "This expression has type ";
                   pp_ty d.actual_ty;
                   print_string " but an expression was expected of type ";
                   pp_ty d.expected_ty;
                   print_newline()
  | TypeErrorPat d -> print_string "This pattern has type ";
                      pp_ty d.actual_ty;
                      print_string " but a pattern was expected of type ";
                      pp_ty d.expected_ty;
                      print_newline()
  | TypeErrorVar d -> print_string "This variable has type ";
                      pp_ty d.actual_ty;
                      print_string " but a variable was expected of type ";
                      pp_ty d.expected_ty;
                      print_newline()
  | UndefinedVariable id -> Printf.printf "Variable not bound: %s" id;
                            print_newline()
  | DuplicateVariable id -> Printf.printf "Variable %s is bound several times in this place" id;
                            print_newline()
  | UnmatchedVariablesInOrPattern id -> Printf.printf "Variable %s must occur on both sides of this | pattern" id;
                                        print_newline()
  | NotFunction { expected_ty = expected_ty } ->
     print_string "This expression should not be a function, the expected type is ";
     pp_ty expected_ty;
     print_newline()
  | NonFunctionApplied { actual_ty = actual_ty } ->
     print_string "This expression has type ";
     pp_ty actual_ty;
     print_newline();
     print_endline "This is not a function; it cannot be applied."
  | UnmatchedParameterType d ->
     print_string "This parameter has ";
     pp_ty d.actual_ty;
     print_string " but a parameter was expected of ";
     pp_ty d.expected_ty;
     print_newline()
  | UndefinedConstructor cid -> Printf.printf "Constructor not bound: %s" cid; print_newline()
  | UnmatchedConstructorArguments { constr_name = cid ; expected_num = ex ; actual_num = ac } ->
     Printf.printf "The constructor %s expects %d argument(s)," cid ex;
     print_newline();
     Printf.printf "but is applied here to %d argument(s)" ac;
     print_newline()
  | DuplicateTypeParameter ty ->
     print_string "The type parameter ";
     pp_ty ty;
     print_endline " occurs several times"

type tyenv = tysc Environment.t
           
let freevar_tyenv tyenv =
  let f tysc s = MySet.union (freevar_tysc tysc) s in
  Environment.fold_right f tyenv MySet.empty

(* s: (named) type variable (e.g. 'a, α) ~> ty *)
let subst_type s ty =
  let rec subst_type' ty (var, t) =
    match ty, var with
    TyInt, _ -> TyInt
  | TyBool, _ -> TyBool
  | TyList ty, _ -> TyList (subst_type' ty (var, t))
  | TyFun (ty1, ty2), _ -> TyFun (subst_type' ty1 (var, t),
                                  subst_type' ty2 (var, t))
  | TyVar alpha, TyVar beta when alpha = beta -> t
  | TyWeakVar alpha, TyWeakVar beta when alpha = beta -> t
  | TyNamedVar id, TyNamedVar id' when id = id' -> t
  | TyVari (id, ty_of_args), _ -> TyVari (id, List.map (fun ty -> subst_type' ty (var, t)) ty_of_args)
  | TyRef ty, _ -> TyRef (subst_type' ty (var, t))
  | TyUnit, _ -> TyUnit
  | _, _ -> ty
  in List.fold_left subst_type' ty s
   
let closure ty tyenv subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
         (fun id -> freevar_ty (subst_type subst (TyVar id)))
         fv_tyenv') in
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
  TyScheme (MySet.to_list ids, ty)

let weaken ty tyenv subst = 
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
         (fun id -> freevar_ty (subst_type subst (TyVar id)))
         fv_tyenv') in
  let ids = MySet.to_list (MySet.diff (freevar_ty ty) fv_tyenv) in
  let map = List.map (fun id -> (TyVar id, TyWeakVar (fresh_tyvar()))) ids in
  subst_type map ty

let instantiate subst tysc =
  let TyScheme(ids, ty) = tysc in
  let rec instantiate' = function
      TyList ty -> TyList (instantiate' ty)
    | TyWeakVar alpha -> subst_type subst (TyWeakVar alpha)
    | TyFun (ty1, ty2) -> TyFun (instantiate' ty1, instantiate' ty2)
    | TyVari (id, tys) -> TyVari (id, List.map instantiate' tys)
    | TyRef ty -> TyRef (instantiate' ty)
    | ty -> ty in
  TyScheme (ids, instantiate' ty)

let eqs_of_subst s = s (* identity function *)

let subst_eqs s eqs = List.map (fun (ty, ty') -> (subst_type s ty, subst_type s ty')) eqs
   
let rec unify = function
    [] -> []
  | ((ty1, ty2) as p) :: rest ->
     let rest = List.filter ((<>) p) rest in
     match ty1, ty2 with
       _, _ when ty1 = ty2 -> unify rest
     | TyFun (ty11, ty12), TyFun (ty21, ty22) ->
        unify ((ty11, ty21) :: (ty12, ty22) :: rest)
     | TyList tye1, TyList tye2 ->
        unify ((tye1, tye2) :: rest)
     | TyVari (id, ty_of_args), TyVari (id', ty_of_args') -> (* variant 型の存在チェックはここでは行なわない *)
        if id <> id'
        then raise Unify
        else unify (List.map2 (fun ty1 ty2 -> (ty1, ty2)) ty_of_args ty_of_args' @ rest)
     | TyRef ty1, TyRef ty2 -> unify ((ty1, ty2) :: rest)
     | TyVar alpha, _ ->
        if MySet.member alpha (freevar_ty ty2)
        then raise Unify
        else let q = (TyVar alpha, ty2) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | _, TyVar alpha ->
        if MySet.member alpha (freevar_ty ty1)
        then raise Unify
        else let q = (TyVar alpha, ty1) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | TyWeakVar alpha, _ ->
        if MySet.member alpha (freeweakvar_ty ty2)
        then raise Unify
        else let q = (TyWeakVar alpha, ty2) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | _, TyWeakVar alpha ->
        if MySet.member alpha (freeweakvar_ty ty1)
        then raise Unify
        else let q = (TyWeakVar alpha, ty1) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | TyNamedVar id, _ ->
        if MySet.member id (namedvar_in_ty ty2)
        then raise Unify
        else let q = (TyNamedVar id, ty2) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | _, TyNamedVar id ->
        if MySet.member id (namedvar_in_ty ty1)
        then raise Unify
        else let q = (TyNamedVar id, ty1) in
             let rest = subst_eqs [q] rest
             in q :: unify rest              
     | _, _ -> raise Unify

let incremental_unify s eqs =
  let eqs = subst_eqs s eqs in
  s @ unify eqs

let ty_prim op =
  match op with
    Plus -> (TyInt, TyInt, TyInt)
  | Mult -> (TyInt, TyInt, TyInt)
  | Lt -> (TyInt, TyInt, TyBool)
  | And -> (TyBool, TyBool, TyBool)
  | Or -> (TyBool, TyBool, TyBool)
  | Append ->
     let ty = TyVar (fresh_tyvar ()) in
     (ty, TyList ty, TyList ty)
  | LAnd -> (TyInt, TyInt, TyInt)
  | Lsr -> (TyInt, TyInt, TyInt)
  | Mod -> (TyInt, TyInt, TyInt)

let rec ty_exp ?expected_ty tyenv tydef subst exp =
  let expected_ty = match expected_ty with
      Some ty -> subst_type !subst ty
    | None -> TyVar (fresh_tyvar ()) in
  match exp.exp_desc with
    Var x ->
     let TyScheme (vars, ty) = try Environment.lookup x tyenv
                               with
                                 Environment.Not_bound -> err exp.exp_loc (UndefinedVariable x) in
     let s = List.map (fun id -> (TyVar id, TyVar (fresh_tyvar ()))) vars in
     let ty = ty |> subst_type s |> subst_type !subst in
     (try subst := incremental_unify !subst [(ty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = ty }));
     subst_type !subst ty
  | ILit _ ->
     (try subst := incremental_unify !subst [(TyInt, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = TyInt }));
     TyInt
  | BLit _ ->
     (try subst := incremental_unify !subst [(TyBool, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = TyBool }));
     TyBool
  | EmptyList ->
     let ty = TyList (TyVar (fresh_tyvar ())) in
     (try subst := incremental_unify !subst [(ty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = ty }));
     subst_type !subst ty
  | BinOp (op, exp1, exp2) ->
     let (argty1, argty2, resty) = ty_prim op in
     let _ = ty_exp ~expected_ty:argty1 tyenv tydef subst exp1 in
     let _ = ty_exp ~expected_ty:argty2 tyenv tydef subst exp2 in
     let expected_ty = subst_type !subst expected_ty in
     (try subst := incremental_unify !subst [(resty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = resty }));
     subst_type !subst resty
  | IfExp (exp1, exp2, exp3) ->
     let _ = ty_exp ~expected_ty:TyBool tyenv tydef subst exp1 in
     let _ = ty_exp ~expected_ty:expected_ty tyenv tydef subst exp2 in
     ty_exp ~expected_ty:expected_ty tyenv tydef subst exp3
  | LetExp (l, exp) ->
     let _ = List.fold_left (fun is (id, loc, _) ->
                 if List.mem id is
                 then err loc (DuplicateVariable id)
                 else id :: is) [] l in
     let tbs = List.fold_left (fun tbs (x, _, e) ->
                   let ty = ty_exp tyenv tydef subst e in
                   let ty = if is_syntactic_value e
                            then ty
                            else weaken ty tyenv !subst in
                   (x, ty) :: tbs) [] l in
     let tyenv' = List.fold_left (fun tyenv' (id, ty) ->
                      let tysc = closure ty tyenv !subst in (* 1つずつ closure を適用する, TyNamedVar _ は∀直後に付けない *)
                      Environment.extend id tysc tyenv') tyenv tbs in
     ty_exp ~expected_ty:expected_ty tyenv' tydef subst exp
  | LetRecExp (l, exp) ->
     let _ = List.fold_left (fun is (id, loc, _, _) ->
                 if List.mem id is
                 then err loc (DuplicateVariable id)
                 else id :: is) [] l in
     (* 引数と戻り値の型の組のリスト *)
     let tys = List.fold_left (fun tys _ -> (TyVar (fresh_tyvar ()), TyVar (fresh_tyvar ())) :: tys) [] l in
     let tyenv' = List.fold_left2 (fun tyenv' (f, _, _, _) (argty, resty) -> (* tyenv + recursive functions *)
                      Environment.extend f (tysc_of_ty (TyFun (argty, resty))) tyenv') tyenv l tys in
     let () = List.iter2 (fun (_, _, x, e) (argty, resty) ->
                  let tyenv'' = Environment.extend x (tysc_of_ty argty) tyenv' in (* tyenv' + argument x of f *)
                  let _ = ty_exp ~expected_ty:resty tyenv'' tydef subst e in ()) l tys in
     let tyenv' = List.fold_left2 (fun tyenv' (f, _, _, _) (argty, resty) ->
                      let tysc = closure (subst_type !subst (TyFun (argty, resty))) tyenv !subst in
                      Environment.extend f tysc tyenv') tyenv l tys in
     ty_exp ~expected_ty:expected_ty tyenv' tydef subst exp
  | FunExp (param, body) ->
     let domty = TyVar (fresh_tyvar ()) in
     let ranty = TyVar (fresh_tyvar ()) in
     let funty = TyFun (domty, ranty) in
     let () = try subst := incremental_unify !subst [(funty, expected_ty)]
              with
                Unify -> err exp.exp_loc (NotFunction { expected_ty = expected_ty }) in
     let domty = subst_type !subst domty in
     let id, domty', loc = match param with
         Param id -> id, TyVar (fresh_tyvar ()), Location.dummy_loc
       | TypedParam (id, ty, loc) -> id, ty, loc in
     let () = try subst := incremental_unify !subst [(domty, domty')]
              with
                Unify -> err loc (UnmatchedParameterType { expected_ty = domty
                                                         ; actual_ty   = domty' }) in
     let tyenv' = Environment.extend id (tysc_of_ty domty) tyenv in
     let _ = ty_exp ~expected_ty:ranty tyenv' tydef subst body in
     subst_type !subst funty
  | AppExp (exp1, exp2) ->
     let alpha = TyVar (fresh_tyvar ()) in
     let beta  = TyVar (fresh_tyvar ()) in
     let funty = TyFun (alpha, beta) in     
     let funty' = ty_exp tyenv tydef subst exp1 in
     let () = try subst := incremental_unify !subst [(funty, funty')]
              with
                Unify -> err exp1.exp_loc (NonFunctionApplied { actual_ty = funty' }) in
     let _ = ty_exp ~expected_ty:alpha tyenv tydef subst exp2 in
     let beta = subst_type !subst beta in
     (try subst := incremental_unify !subst [(expected_ty, beta)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = beta }));
     subst_type !subst beta
  | MatchExp (exp, pm) ->
     let ty0 = ty_exp tyenv tydef subst exp in
     let () =
       List.iter (fun (pat, e) ->
           let (_, tbs) = ty_pattern ~expected_ty:ty0 tydef subst pat in
           let tyenv' = List.fold_left (fun tyenv' (id, _, ty) ->
                            let ty = if is_syntactic_value exp then ty else weaken ty tyenv !subst in
                            let tysc = closure ty tyenv !subst in
                            Environment.extend id tysc tyenv') tyenv tbs in
           let _ = ty_exp ~expected_ty:expected_ty tyenv' tydef subst e in ()) pm in
     subst_type !subst expected_ty
  | TypedExp (inner_exp, expected_ty') ->
     let ty = ty_exp ~expected_ty:expected_ty' tyenv tydef subst inner_exp in
     let expected_ty = subst_type !subst expected_ty in
     (try subst := incremental_unify !subst [(ty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty = ty }));
     subst_type !subst ty
  | VariExp (cid, es) ->
     let (ty_of_args, id, ps) = try Environment.lookup cid tydef (* コンストラクタの存在を確認 *)
                                with
                                  Environment.Not_bound -> err (* TODO: correct location *) exp.exp_loc (UndefinedConstructor cid) in
     let () = (* 与えられている引数とコンストラクタの引数の個数が等しいか確認 *)
       if List.length es <> List.length ty_of_args
       then err exp.exp_loc (UnmatchedConstructorArguments { constr_name = cid
                                                           ; expected_num = List.length ty_of_args
                                                           ; actual_num = List.length es }) in
     let ps' = List.map (fun _ -> TyVar(fresh_tyvar())) ps in
     let ty = TyVari(id, ps') in
     let () =
       try subst := incremental_unify !subst [(ty, expected_ty)]
       with
         Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                             ; actual_ty   = ty }) in
     let s = List.combine ps ps' in
     let ty_of_args = List.map (subst_type s) ty_of_args in
     let () = List.iter2 (fun e ty -> ignore (ty_exp ~expected_ty:ty tyenv tydef subst e)) es ty_of_args in
     subst_type !subst ty
  | RefExp exp1 ->
     let cty = ty_exp tyenv tydef subst exp1 in
     let ty = TyRef cty in
     let expected_ty = subst_type !subst expected_ty in
     let () =
       try subst := incremental_unify !subst [(ty, expected_ty)]
       with
         Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                             ; actual_ty   = ty }) in
     subst_type !subst ty
  | AssnExp(exp1, exp2) ->
     let () =
       try subst := incremental_unify !subst [(TyUnit, expected_ty)]
       with
         Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                             ; actual_ty = TyUnit }) in
     let alpha = TyVar (fresh_tyvar()) in
     let () = ignore (ty_exp ~expected_ty:(TyRef alpha) tyenv tydef subst exp1) in
     let () = ignore (ty_exp ~expected_ty:alpha tyenv tydef subst exp2) in
     TyUnit
  | DerefExp exp1 ->
     let alpha = TyVar (fresh_tyvar()) in
     let () = ignore (ty_exp ~expected_ty:(TyRef alpha) tyenv tydef subst exp1) in
     let expected_ty = subst_type !subst expected_ty in
     let () =
       try subst := incremental_unify !subst [(alpha, expected_ty)]
       with
         Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                             ; actual_ty = alpha }) in
     subst_type !subst alpha
  | UnitExp ->
     let () =
       try subst := incremental_unify !subst [(TyUnit, expected_ty)]
       with
         Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                             ; actual_ty   = TyUnit }) in
     TyUnit

(* Return value: the type of pattern, type-bindings obtained by pattern *)
and ty_pattern ?expected_ty tydef subst pat = 
  let expected_ty = match expected_ty with
      Some ty -> subst_type !subst ty
    | None    -> TyVar (fresh_tyvar ()) in
  match pat.Pattern.pat_desc with
    Pattern.Var x -> (expected_ty, [(x, pat.Pattern.pat_loc, expected_ty)])
  | Pattern.Ignore -> (expected_ty, [])
  | Pattern.ILit _ ->
     let () = try subst := incremental_unify !subst [(TyInt, expected_ty)]
              with
                Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                               ; actual_ty   = TyInt }) in
     (TyInt, [])
  | Pattern.BLit _ ->
     let () = try subst := incremental_unify !subst [(TyBool, expected_ty)]
              with
                Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                               ; actual_ty   = TyBool }) in
     (TyBool, [])
  | Pattern.EmptyList ->
     let ty = TyList (TyVar (fresh_tyvar ())) in
     let () = try subst := incremental_unify !subst [(ty, expected_ty)]
              with
                Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                               ; actual_ty   = ty }) in
     (subst_type !subst ty, [])
  | Pattern.Or (pat1, pat2) ->
     let (_ , tbs1) = ty_pattern ~expected_ty:expected_ty tydef subst pat1 in
     let (ty, tbs2) = ty_pattern ~expected_ty:expected_ty tydef subst pat2 in
     let () =
       List.iter (fun (id, _, ty1) ->
           let (_, loc, ty2) = try List.find (fun (id', _, _) -> id' = id) tbs2
                               with
                                 Not_found -> err pat.Pattern.pat_loc (UnmatchedVariablesInOrPattern id) in
           let ty1 = subst_type !subst ty1 in
           let ty2 = subst_type !subst ty2 in
           try subst := incremental_unify !subst [(ty1, ty2)]
           with
             Unify -> err loc (TypeErrorVar { expected_ty = ty1
                                            ; actual_ty   = ty2 })) tbs1 in
     let tbs = List.map (fun (id, loc, ty) -> (id, loc, subst_type !subst ty)) tbs1 in
     (subst_type !subst ty, tbs)
  | Pattern.Append (pat1, pat2) ->
     let alpha = TyVar (fresh_tyvar ()) in
     let () =
       try subst := incremental_unify !subst [(TyList alpha, expected_ty)]
       with
         Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                        ; actual_ty   = TyList alpha }) in
     let (_, tbs1) = ty_pattern ~expected_ty:alpha tydef subst pat1 in
     let (_, tbs2) = ty_pattern ~expected_ty:(TyList alpha) tydef subst pat2 in
     let () =
       List.iter (fun (id, _, _) ->
           try
             let (_, loc, _) = List.find (fun (id', _, _) -> id' = id) tbs2 in
             err loc (DuplicateVariable id)
           with
             Not_found -> ()) tbs1 in
     let tbs1 = List.map (fun (id, loc, ty) -> (id, loc, subst_type !subst ty)) tbs1 in
     (subst_type !subst expected_ty, tbs1 @ tbs2)
  | Pattern.Vari (cid, pats) ->
     let (ty_of_args, id, params) = try Environment.lookup cid tydef (* コンストラクタの存在を確認 *)
                                    with
                                      Environment.Not_bound -> err pat.Pattern.pat_loc (UndefinedConstructor cid) in
     let () = (* 与えられている引数とコンストラクタの引数の個数が等しいか確認 *)
       if List.length pats <> List.length ty_of_args
       then err pat.Pattern.pat_loc (UnmatchedConstructorArguments { constr_name = cid ; expected_num = List.length ty_of_args ; actual_num = List.length pats }) in
     let params' = List.map (fun _ -> TyVar(fresh_tyvar())) params in
     let ty = TyVari(id, params') in
     let () =
       try subst := incremental_unify !subst [(ty, expected_ty)]
       with
         Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                        ; actual_ty   = ty }) in
     let s = List.combine params params' in
     let ty_of_args = List.map (subst_type s) ty_of_args in
     let tbs = List.fold_left2 (fun tbs ty pat -> 
                   let (_, tbs') = ty_pattern ~expected_ty:ty tydef subst pat in
                   let () = List.iter (fun (id, _, _) ->
                                match List.find_opt (fun (id', _, _) -> id' = id) tbs' with (* 引数が重複していないか確認 *)
                                  Some (_, loc, _) -> err loc (DuplicateVariable id)
                                | None -> ()) tbs in
                   tbs' @ tbs) [] ty_of_args pats in
     (subst_type !subst ty, tbs)
  | Pattern.Unit ->
     let actual_ty = TyUnit in
     let () =
       try subst := incremental_unify !subst [(actual_ty, expected_ty)]
       with
         Unify -> err pat.Pattern.pat_loc (TypeErrorPat { expected_ty = expected_ty
                                                        ; actual_ty   = actual_ty }) in
     (actual_ty, [])
     
let rec ty_decl tyenv tydef = function
    Exp e -> 
    let subst = ref [] in
    let ty = ty_exp tyenv tydef subst e in 
    let tyenv = Environment.map (instantiate !subst) tyenv in (* weak type variable の正体が分かったときに型環境を更新するために必要 *)
    (tyenv, tydef, [ty])
  | Decl l ->
     let _ = List.fold_left (fun is (id, loc, _) ->
                 if List.mem id is
                 then err loc (DuplicateVariable id)
                 else id :: is) [] l in
     let subst = ref [] in
     let tbs = List.fold_left (fun tbs (id, _, e) ->
                   let ty = ty_exp tyenv tydef subst e in
                   let ty = if is_syntactic_value e
                            then ty
                            else weaken ty tyenv !subst in (* 型変数を「弱める」 *)
                   (id, ty) :: tbs) [] l in
     let tbs = List.rev @@ List.map (fun (id, ty) -> (id, subst_type !subst ty)) tbs in
     let cor = (* TyNamedVar _ -> TyVar _ *)
       List.fold_left (fun s (_, ty) -> MySet.union s (namedvar_in_ty ty)) MySet.empty tbs
       |> MySet.to_list
       |> List.map (fun id -> (TyNamedVar id, TyVar (fresh_tyvar ()))) in
     let tbs = List.map (fun (id, ty) -> (id, subst_type cor ty)) tbs in
     let tyenv' = List.fold_left (fun tyenv' (id, ty) ->
                      let tysc = closure ty tyenv !subst (* 1つずつ closure を適用する *) in
                      Environment.extend id tysc tyenv') tyenv tbs in
     let tyenv' = Environment.map (instantiate !subst) tyenv' in
     (tyenv', tydef, List.map snd tbs)
  | RecDecl l ->
     let _ = List.fold_left (fun is (id, loc, _, _) ->
                 if List.mem id is
                 then err loc (DuplicateVariable id)
                 else id :: is) [] l in
     let subst = ref [] in
     let tys = List.fold_left (fun tys _ -> (TyVar (fresh_tyvar ()), TyVar (fresh_tyvar ())) :: tys) [] l in
     let tyenv' = List.fold_left2 (fun tyenv' (f, _, _, _) (argty, resty) ->
                      Environment.extend f (tysc_of_ty (TyFun (argty, resty))) tyenv') tyenv l tys in
     let () = List.iter2 (fun (_, _, x, e) (argty, resty) ->
                  let tyenv'' = Environment.extend x (tysc_of_ty argty) tyenv' in
                  let _ = ty_exp ~expected_ty:resty tyenv'' tydef subst e in ()) l tys in
     let tys = List.map (fun (argty, resty) -> subst_type !subst (TyFun (argty, resty))) tys in
     let cor = (* TyNamedVar _ -> TyVar _ *)
       List.fold_left (fun s ty -> MySet.union s (namedvar_in_ty ty)) MySet.empty tys
       |> MySet.to_list
       |> List.map (fun id -> (TyNamedVar id, TyVar (fresh_tyvar()))) in
     let tys = List.map (fun ty -> subst_type cor ty) tys in
     let tyenv' = List.fold_left2 (fun tyenv' (f, _, _, _) ty ->
                      Environment.extend f (closure ty tyenv !subst) tyenv') tyenv l tys in
     let tyenv' = Environment.map (instantiate !subst) tyenv' in
     (tyenv', tydef, tys)
  | Seq progs -> (* 宣言と型定義の混合に対応済み (パーサーエラーになるので書けない) *)
     let (newtyenv, _, tys) = List.fold_left (fun (tyenv, tydef, tys) prog ->
                                         let (tyenv', tydef', tys') = ty_decl tyenv tydef prog in
                                         (tyenv', tydef', tys @ tys')) (tyenv, tydef, []) progs in
     (newtyenv, tydef, tys)
  | TyDef (VDef (id, ps, cs)) -> (* 型定義は型推論時に読み込む *)
     let rec check_unique l =
       match l with
         [] | [_] -> ()
       | (p, _) :: l -> match List.find_opt (fun (p', _) -> p' = p) l with
                          Some (_, loc) -> err loc (DuplicateTypeParameter p)
                        | _ -> check_unique l in
     let () = check_unique ps in
     let ps = List.map (fun (p, _) -> p) ps in
     let tydef = List.fold_left (fun tydef (cid, tys) -> Environment.extend cid (tys, id, ps) tydef) tydef cs in
     (tyenv, tydef, [])

(* for test of Exercise 4.3.2 *)
type subst = (tyvar * ty) list

let subst_type s ty =
  let s = List.map (fun (alpha, t) -> (TyVar alpha, t)) s in
  subst_type s ty
