%{
open Syntax
open Location

let mkloc ls le =
  { loc_start = ls; loc_end = le }
   
let mkexp d ls le =
  { exp_desc = d
  ; exp_loc = mkloc ls le
  }
  
let ghexp d =
  { exp_desc = d
  ; exp_loc = dummy_loc
  }
  
let mkpat d ls le =
  { Pattern.pat_desc = d
  ; Pattern.pat_loc = mkloc ls le
  }

let ghpat d =
  { Pattern.pat_desc = d
  ; Pattern.pat_loc = dummy_loc
  }
  
let reloc_exp e ls le =
  { e with exp_loc = mkloc ls le }

let reloc_pat p ls le =
  { p with Pattern.pat_loc = mkloc ls le }
  
let infix_op_to_funexp op =
  FunExp (Param "x",
          ghexp (FunExp (Param "y",
                         ghexp (BinOp (op, ghexp (Var "x"), ghexp (Var "y"))))))
         
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MULT LT
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ AND REC
%token LAND LOR
%token FUN RARROW
%token LSBRACKET RSBRACKET APPEND MATCH WITH BAR SEMI
%token UNDERSCORE
%token COLON APOSTROPHE INT BOOL LIST
%token TYPE OF COMMA
%token REF UNIT ASSN DEREF
%token LAND2 LSR MOD

%token <int> INTV
%token <Syntax.id> ID CID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | ds=nonempty_list(s=LetDecl { Decl s } | s=LetRecDecl { RecDecl s }) SEMISEMI { Seq ds }
  | d=TypeDef SEMISEMI { TyDef d }

LetDecl :
    p=LetHead ps=LetAnd* { p :: ps }

LetRecDecl :
    t=LetRecHead ts=LetRecAnd* { t :: ts }

LetHead :
    LET x=ID EQ e=Expr { (x, mkloc $startpos(x) $endpos(x), e) }
  | LET x=ID COLON te=TypeExpr EQ e=Expr
    { (x, mkloc $startpos(x) $endpos(x) , mkexp (TypedExp (e, te)) e.exp_loc.loc_start e.exp_loc.loc_end) }
  | LET f=ID xs=Parameter+ EQ e=Expr
    { let e' = List.fold_right (fun param body -> ghexp (FunExp (param, body))) xs e in
      (f, mkloc $startpos(f) $endpos(f), reloc_exp e' e.exp_loc.loc_start e.exp_loc.loc_end) }
  | LET f=ID xs=Parameter+ COLON te=TypeExpr EQ e=Expr
    { let e' = List.fold_right (fun param body -> ghexp (FunExp (param, body)))
                               xs
                               (mkexp (TypedExp (e, te)) e.exp_loc.loc_start e.exp_loc.loc_end) in
      (f, mkloc $startpos(f) $endpos(f), reloc_exp e' e.exp_loc.loc_start e.exp_loc.loc_end) }

LetAnd :
    AND x=ID EQ e=Expr { (x, mkloc $startpos(x) $endpos(x), e) }
  | AND x=ID COLON te=TypeExpr EQ e=Expr
    { (x, mkloc $startpos(x) $endpos(x), mkexp (TypedExp (e, te)) e.exp_loc.loc_start e.exp_loc.loc_end) }
  | AND f=ID xs=Parameter+ EQ e=Expr
    { let e' = List.fold_right (fun param body -> ghexp (FunExp (param, body))) xs e in
      (f, mkloc $startpos(f) $endpos(f), reloc_exp e' e.exp_loc.loc_start e.exp_loc.loc_end) }
  | AND f=ID xs=Parameter+ COLON te=TypeExpr EQ e=Expr
    { let e' = List.fold_right (fun param body -> ghexp (FunExp (param, body)))
                               xs
                               (mkexp (TypedExp (e, te)) e.exp_loc.loc_start e.exp_loc.loc_end) in
      (f, mkloc $startpos(f) $endpos(f), reloc_exp e' e.exp_loc.loc_start e.exp_loc.loc_end) }

LetRecHead :
    LET REC x=ID EQ FUN y=ID RARROW body=Expr { (x, mkloc $startpos(x) $endpos(x), y, body) }

LetRecAnd :
    AND x=ID EQ FUN y=ID RARROW body=Expr { (x, mkloc $startpos(x) $endpos(x), y, body) }

(* --------------- Expressions --------------- *)
Expr :
    e=LetExpr { e }
  | e=LetRecExpr { e }
  | e=MatchExpr { e }
  | e=FunExpr { e }
  | e=SeqExpr { e }   

LetExpr :
    s=LetDecl IN e2=Expr { mkexp (LetExp (s, e2)) $symbolstartpos $endpos }

LetRecExpr :
    s=LetRecDecl IN e=Expr { mkexp (LetRecExp (s, e)) $symbolstartpos $endpos }

FunExpr :
    FUN xs=Parameter+ RARROW e=Expr
    { reloc_exp (List.fold_right (fun param body -> ghexp (FunExp (param, body))) xs e) $symbolstartpos $endpos }

MatchExpr :
    MATCH e=Expr WITH p=PatternMatching { mkexp (MatchExp (e, p)) $symbolstartpos $endpos }

PatternMatching :
    BAR? ps=separated_nonempty_list(BAR, Case) { ps }

Case :
    p=Pattern RARROW e=Expr { (p, e) }

SeqExpr :
    l=IfExpr SEMI r=SeqExpr { ghexp (MatchExp(l, [(ghpat Pattern.Ignore, r)])) }
  | l=AssnExpr SEMI r=SeqExpr { ghexp (MatchExp(l, [(ghpat Pattern.Ignore, r)])) }
  | e=IfExpr { e }
  | e=AssnExpr { e }

IfExpr :
    IF e1=Expr THEN e2=Expr ELSE e3=IfExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }
  | IF e1=Expr THEN e2=Expr ELSE e3=AssnExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }
  | IF e1=Expr THEN e2=Expr ELSE e3=LetExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }
  | IF e1=Expr THEN e2=Expr ELSE e3=LetRecExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }
  | IF e1=Expr THEN e2=Expr ELSE e3=MatchExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }
  | IF e1=Expr THEN e2=Expr ELSE e3=FunExpr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }

AssnExpr :
    l=OrExpr ASSN r=AssnExpr   { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | l=OrExpr ASSN r=IfExpr     { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | l=OrExpr ASSN r=LetExpr    { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | l=OrExpr ASSN r=LetRecExpr { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | l=OrExpr ASSN r=MatchExpr  { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | l=OrExpr ASSN r=FunExpr    { mkexp (AssnExp(l, r)) $symbolstartpos $endpos }
  | e=OrExpr { e }

OrExpr :
    l=AndExpr LOR r=OrExpr     { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | l=AndExpr LOR r=IfExpr     { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | l=AndExpr LOR r=LetExpr    { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | l=AndExpr LOR r=LetRecExpr { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | l=AndExpr LOR r=MatchExpr  { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | l=AndExpr LOR r=FunExpr    { mkexp (BinOp (Or, l, r)) $symbolstartpos $endpos }
  | e=AndExpr { e }
   
AndExpr :
    l=LTExpr LAND r=AndExpr    { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LAND r=IfExpr     { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LAND r=LetExpr    { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LAND r=LetRecExpr { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LAND r=MatchExpr  { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LAND r=FunExpr    { mkexp (BinOp (And, l, r)) $symbolstartpos $endpos }
  | e=LTExpr { e }

LTExpr :
    l=LTExpr LT r=ConsExpr   { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LT r=IfExpr     { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LT r=LetExpr    { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LT r=LetRecExpr { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LT r=MatchExpr  { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | l=LTExpr LT r=FunExpr    { mkexp (BinOp (Lt, l, r)) $symbolstartpos $endpos }
  | e=ConsExpr { e }

ConsExpr :
    l=PExpr APPEND r=ConsExpr    { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | l=PExpr APPEND r=IfExpr      { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | l=PExpr APPEND r=LetExpr     { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | l=PExpr APPEND r=LetRecExpr  { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | l=PExpr APPEND r=MatchExpr   { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | l=PExpr APPEND r=FunExpr     { mkexp (BinOp (Append, l, r)) $symbolstartpos $endpos }
  | e=PExpr { e }

PExpr :
    l=PExpr PLUS r=ModExpr      { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | l=PExpr PLUS r=IfExpr     { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | l=PExpr PLUS r=LetExpr    { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | l=PExpr PLUS r=LetRecExpr { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | l=PExpr PLUS r=MatchExpr  { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | l=PExpr PLUS r=FunExpr    { mkexp (BinOp (Plus, l, r)) $symbolstartpos $endpos }
  | e=ModExpr { e }

ModExpr :
    l=ModExpr MOD r=MExpr      { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | l=ModExpr MOD r=IfExpr     { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | l=ModExpr MOD r=LetExpr    { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | l=ModExpr MOD r=LetRecExpr { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | l=ModExpr MOD r=MatchExpr  { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | l=ModExpr MOD r=FunExpr    { mkexp (BinOp (Mod, l, r)) $symbolstartpos $endpos }
  | e=MExpr { e }

MExpr :
    l=MExpr MULT r=LAndExpr    { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | l=MExpr MULT r=IfExpr     { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | l=MExpr MULT r=LetExpr    { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | l=MExpr MULT r=LetRecExpr { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | l=MExpr MULT r=MatchExpr  { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | l=MExpr MULT r=FunExpr    { mkexp (BinOp (Mult, l, r)) $symbolstartpos $endpos }
  | e=LAndExpr { e }

LAndExpr :
    l=LAndExpr LAND2 r=LSRExpr    { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | l=LAndExpr LAND2 r=IfExpr     { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | l=LAndExpr LAND2 r=LetExpr    { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | l=LAndExpr LAND2 r=LetRecExpr { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | l=LAndExpr LAND2 r=MatchExpr  { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | l=LAndExpr LAND2 r=FunExpr    { mkexp (BinOp (LAnd, l, r)) $symbolstartpos $endpos }
  | e=LSRExpr { e }

LSRExpr :
    l=LSRExpr LSR r=AppExpr   { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | l=LSRExpr LSR r=IfExpr     { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | l=LSRExpr LSR r=LetExpr    { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | l=LSRExpr LSR r=LetRecExpr { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | l=LSRExpr LSR r=MatchExpr  { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | l=LSRExpr LSR r=FunExpr    { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos }
  | e=AppExpr { e }

AppExpr :
    e=FunAppExpr { e }
  | e=ConstrAppExpr { e }
  | e=AExpr { e }

FunAppExpr :
    l=FunAppExpr r=AExpr { mkexp (AppExp (l, r)) $symbolstartpos $endpos }
  | l=AExpr r=AExpr { mkexp (AppExp (l, r)) $symbolstartpos $endpos }
  | REF e=AExpr { mkexp (RefExp e) $symbolstartpos $endpos }

ConstrAppExpr :
    id=CID e=AExpr { mkexp (VariExp (id, [e])) $symbolstartpos $endpos }
  | id=CID LPAREN e1=Expr COMMA es=separated_nonempty_list(COMMA, Expr) RPAREN { mkexp (VariExp (id, e1 :: es)) $symbolstartpos $endpos }

AExpr :
    i=INTV { mkexp (ILit i) $symbolstartpos $endpos }
  | TRUE   { mkexp (BLit true) $symbolstartpos $endpos }
  | FALSE  { mkexp (BLit false) $symbolstartpos $endpos }
  | LPAREN RPAREN { mkexp UnitExp $symbolstartpos $endpos }
  | i=ID   { mkexp (Var i) $symbolstartpos $endpos }
  | e=InfixOp { e }
  | LPAREN e=Expr RPAREN { e }
  | LPAREN e=Expr COLON te=TypeExpr RPAREN { mkexp (TypedExp (e, te)) $symbolstartpos $endpos }
  | e=ListExpr { e }
  | DEREF e=AExpr { mkexp (DerefExp e) $symbolstartpos $endpos }
  | id=CID { mkexp (VariExp (id, [])) $symbolstartpos $endpos }

ListExpr :
    LSBRACKET RSBRACKET { mkexp EmptyList $symbolstartpos $endpos }
  | LSBRACKET es=separated_nonempty_list(SEMI, e=IfExpr | e=AssnExpr | e=LetExpr | e=LetRecExpr | e=MatchExpr | e=FunExpr { e }) RSBRACKET { List.fold_right (fun e t -> ghexp (BinOp (Append, e, t))) es (ghexp EmptyList) }

  /* TODO: 不要なら消す */
  /* | l=LSRExpr LSR r=IfExpr     { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos } */
  /* | l=LSRExpr LSR r=LetExpr    { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos } */
  /* | l=LSRExpr LSR r=LetRecExpr { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos } */
  /* | l=LSRExpr LSR r=MatchExpr  { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos } */
  /* | l=LSRExpr LSR r=FunExpr    { mkexp (BinOp (Lsr, l, r)) $symbolstartpos $endpos } */

InfixOp :
    LPAREN PLUS RPAREN { ghexp (infix_op_to_funexp Plus) }
  | LPAREN MULT RPAREN { ghexp (infix_op_to_funexp Mult) }
  | LPAREN LT RPAREN { ghexp (infix_op_to_funexp Lt) }
  | LPAREN LAND RPAREN { ghexp (infix_op_to_funexp And) }
  | LPAREN LOR RPAREN { ghexp (infix_op_to_funexp Or) }
  | LPAREN APPEND RPAREN { ghexp (infix_op_to_funexp Append) }

(* --------------- Patterns --------------- *)
Pattern :
    p1=APattern BAR p2=Pattern { mkpat (Pattern.Or (p1, p2)) $symbolstartpos $endpos }
  | p1=APattern APPEND p2=Pattern { mkpat (Pattern.Append (p1, p2)) $symbolstartpos $endpos }
  | id=CID { mkpat (Pattern.Vari (id, [])) $symbolstartpos $endpos }
  | id=CID p=Pattern { mkpat (Pattern.Vari (id, [p])) $symbolstartpos $endpos }
  | id=CID LPAREN p1=Pattern COMMA ps=separated_nonempty_list(COMMA, Pattern) RPAREN { mkpat (Pattern.Vari (id, p1 :: ps)) $symbolstartpos $endpos }
  | p=APattern { p }

APattern :
    i=INTV { mkpat (Pattern.ILit i) $symbolstartpos $endpos }
  | TRUE { mkpat (Pattern.BLit true) $symbolstartpos $endpos }
  | FALSE { mkpat (Pattern.BLit false) $symbolstartpos $endpos }
  | LPAREN RPAREN { mkpat Pattern.Unit $symbolstartpos $endpos }
  | i=ID { mkpat (Pattern.Var i) $symbolstartpos $endpos }
  | UNDERSCORE { mkpat (Pattern.Ignore) $symbolstartpos $endpos }
  | LPAREN p=Pattern RPAREN { p }
  | p=ListPattern { p }

ListPattern :
    LSBRACKET RSBRACKET { mkpat Pattern.EmptyList $symbolstartpos $endpos }
  | LSBRACKET ps=separated_nonempty_list(SEMI, Pattern) RSBRACKET
    {
      let p = List.fold_right (fun p acc -> mkpat (Pattern.Append (p, acc)) p.Pattern.pat_loc.loc_start $endpos($3))
                              ps
                              (ghpat Pattern.EmptyList) in
      reloc_pat p $symbolstartpos $endpos
    }

(* --------------- Types --------------- *)
Parameter :
    LPAREN id=ID COLON te=TypeExpr RPAREN { TypedParam (id, te, mkloc $startpos(te) $endpos(te)) }
  | id=ID { Param id }

TypeExpr :
    l=TypeConstr RARROW r=TypeExpr { TyFun (l, r) }
  | te=TypeConstr { te }

TypeConstr :
    te=TypeConstr REF { TyRef te }
  | te=TypeConstr LIST { TyList te }
  | id=ID { TyVari (id, []) }
  | te=TypeConstr id=ID { TyVari (id, [te]) }
  | LPAREN te1=TypeExpr COMMA tes=separated_nonempty_list(COMMA, TypeExpr) RPAREN id=ID { TyVari (id, te1 :: tes) }
  | te=TypeAExpr { te }

TypeAExpr :
    p=TypeParam { p }
  | INT { TyInt }
  | BOOL { TyBool }
  | UNIT { TyUnit }
  | LPAREN te=TypeExpr RPAREN { te }

TypeParam :
    APOSTROPHE id=ID { TyNamedVar id }

TypeDef :
    TYPE ps=TypeParams? id=ID EQ BAR? cs=separated_nonempty_list(BAR, Constructor)
    { match ps with
        Some ps -> VDef(id, ps, cs)
      | None    -> VDef(id, [], cs)
    }

Constructor :
    cid=CID { (cid, []) }
  | cid=CID OF tes=ArgTypes { (cid, tes) }

TypeParams :
    p=TypeParam { [(p, mkloc $startpos(p) $endpos(p))] }
  | LPAREN ps=separated_nonempty_list(COMMA, p=TypeParam { (p, mkloc $startpos(p) $endpos(p)) }) RPAREN { ps }

ArgTypes :
    tes=separated_nonempty_list(MULT, te=TypeConstr { te }) { tes }
