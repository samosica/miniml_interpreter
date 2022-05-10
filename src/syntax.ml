(* ML interpreter / type reconstruction *)
type id = string

type tyvar = int
       
type ty =
  TyInt
| TyBool
| TyList of ty
| TyVar of tyvar
| TyWeakVar of tyvar
| TyNamedVar of id
| TyFun of ty * ty
| TyVari of id * ty list
| TyRef of ty
| TyUnit

type parameter =
  Param of id
| TypedParam of id * ty * Location.t
        
type binOp = Plus | Mult | Lt | And | Or | Append | LAnd | Lsr | Mod

module Pattern = struct
  type pattern =
    { pat_desc : pattern_desc
    ; pat_loc  : Location.t
    }
    
  and pattern_desc =
      Var of id
    | Ignore
    | ILit of int
    | BLit of bool
    | EmptyList
    | Or of pattern * pattern
    | Append of pattern * pattern
    | Vari of id * pattern list
    | Unit
end 

type exp = { exp_desc : exp_desc
           ; exp_loc  : Location.t
           }
               
and exp_desc =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | EmptyList
  | BinOp of binOp * exp * exp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | IfExp of exp * exp * exp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
           
  | LetExp of (id * Location.t * exp) list * exp
  | LetRecExp of (id * Location.t * id * exp) list * exp
  | FunExp of parameter * exp
  | AppExp of exp * exp
  | MatchExp of exp * (Pattern.pattern * exp) list
  | TypedExp of exp * ty
  | VariExp of id * exp list (* コンストラクタ名, 引数のリスト *)
  | RefExp of exp
  | AssnExp of exp * exp
  | DerefExp of exp
  | UnitExp

type tydef =
  VDef of id * (ty * Location.t) list * (id * ty list) list (* variants (name, type parameter, constructor (name, types of arguments)) *)

type program = 
  Exp of exp
| Decl of (id * Location.t * exp) list (* simultaneous declaration *)
| RecDecl of (id * Location.t * id * exp) list (* simultaneous declaration *)
| Seq of program list
| TyDef of tydef
         
type tysc = TyScheme of tyvar list * ty

let tysc_of_ty ty = TyScheme ([], ty)
         
let rec pp_ty = function
    TyInt -> print_string "int"
  | TyBool -> print_string "bool"
  | TyList ty -> pp_ty ty; print_string " list"
  | TyVar n ->
     let c = Char.chr (n mod 26 + Char.code 'a') in
     let m = n / 26 in
     if m = 0
     then begin
         print_char '\'';
         print_char c
       end
     else begin
         print_char '\'';
         print_char c;
         print_int m
       end
  | TyWeakVar n ->
     let c = Char.chr (n mod 26 + Char.code 'a') in
     let m = n / 26 in
     if m = 0
     then begin
         print_string "\'_";
         print_char c
       end
     else begin
         print_string "\'_";
         print_char c;
         print_int m
       end
  | TyNamedVar id ->
     print_char '\'';
     print_string id
  | TyFun (t1, t2) ->
     (match t1 with
        TyFun _ -> print_char '('; pp_ty t1; print_char ')'
      | _ -> pp_ty t1);
     print_string " -> ";
     pp_ty t2
  | TyVari (id, tys) ->
     (match tys with
       [] -> print_string id
      | [TyFun(_, _) as ty] -> print_char '('; pp_ty ty; print_string (") " ^ id)
      | [ty] -> pp_ty ty; print_string (" " ^ id)
      | ty :: tys -> print_char '('; pp_ty ty; List.iter (fun ty -> print_string ", "; pp_ty ty) tys; print_string (") " ^ id))
  | TyRef ty -> 
     (match ty with
        TyFun(_, _) -> print_char '('; pp_ty ty; print_char ')'; print_string " ref"
      | _ -> pp_ty ty; print_string " ref")
  | TyUnit -> print_string "unit"
            
let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body

let rec freevar_ty ty =
  match ty with
    TyInt -> MySet.empty
  | TyBool -> MySet.empty
  | TyList ty -> freevar_ty ty
  | TyVar alpha -> MySet.singleton alpha
  | TyWeakVar _ -> MySet.empty
  | TyNamedVar _ -> MySet.empty
  | TyFun (ty1, ty2) ->
     MySet.union (freevar_ty ty1) (freevar_ty ty2)
  | TyVari (_, tys) ->
     List.fold_right (fun ty s -> MySet.union (freevar_ty ty) s) tys MySet.empty
  | TyRef ty -> freevar_ty ty
  | TyUnit -> MySet.empty

let freevar_tysc = function
    TyScheme (tys, ty) -> MySet.diff (freevar_ty ty) (MySet.from_list tys)

let rec freeweakvar_ty ty =
  match ty with
    TyInt -> MySet.empty
  | TyBool -> MySet.empty
  | TyList ty -> freeweakvar_ty ty
  | TyVar _ -> MySet.empty
  | TyWeakVar alpha -> MySet.singleton alpha
  | TyNamedVar _ -> MySet.empty
  | TyFun (ty1, ty2) ->
     MySet.union (freeweakvar_ty ty1) (freeweakvar_ty ty2)
  | TyVari (_, tys) ->
     List.fold_right (fun ty s -> MySet.union (freeweakvar_ty ty) s) tys MySet.empty
  | TyRef ty -> freeweakvar_ty ty
  | TyUnit -> MySet.empty

let rec namedvar_in_ty ty =
  match ty with
    TyInt -> MySet.empty
  | TyBool -> MySet.empty
  | TyList ty -> namedvar_in_ty ty
  | TyVar _ -> MySet.empty
  | TyWeakVar _ -> MySet.empty
  | TyNamedVar id -> MySet.singleton id
  | TyFun (ty1, ty2) ->
     MySet.union (namedvar_in_ty ty1) (namedvar_in_ty ty2)
  | TyVari (_, tys) ->
     List.fold_right (fun ty s -> MySet.union (namedvar_in_ty ty) s) tys MySet.empty
  | TyRef ty -> namedvar_in_ty ty
  | TyUnit -> MySet.empty

let rec is_syntactic_value exp =
  match exp.exp_desc with
    Var _ | ILit _ | BLit _ | EmptyList | FunExp _ | UnitExp -> true
    | BinOp(Append, exp1, exp2) -> is_syntactic_value exp1 && is_syntactic_value exp2
    | TypedExp(exp, _) -> is_syntactic_value exp
    | VariExp(_, exps) -> List.for_all is_syntactic_value exps
    | _ -> false

let print_constr_decl (cid, ty_of_args) =
  let pp_ty ty =
    match ty with (* コンストラクタの引数に関数型が現れるときは括弧を付けて表示する *)
      TyFun _ -> print_char '('; pp_ty ty; print_char ')'
    | _ -> pp_ty ty in
  print_string cid;
  match ty_of_args with
    [] -> ()
  | ty :: ty_of_args ->
     print_string " of ";
     pp_ty ty;
     List.iter (fun ty ->
         print_string " * ";
         pp_ty ty) ty_of_args

let print_typarams ps =
  match ps with
    [] -> ()
  | [(p, _)] -> pp_ty p
  | (p, _) :: ps -> print_char '(';
                    pp_ty p;
                    List.iter (fun (p, _) ->
                        print_string ", ";
                        pp_ty p) ps;
                    print_char ')'

let print_tydef = function
    VDef (id, ps, cs) ->
      print_string "type ";
      print_typarams ps;
      (match ps with
         [] -> ()
       | _ -> print_char ' ');
      print_string id;
      print_string " = ";
      (match cs with
         [] -> ()
       | c :: cs ->
          print_constr_decl c;
          List.iter (fun c ->
              print_string " | ";
              print_constr_decl c) cs);
      print_newline()
