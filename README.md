# miniml_interpreter
OCamlのサブセットを実装したインタプリタ

[kuis-isle3sw/IoPLMaterials](https://github.com/kuis-isle3sw/IoPLMaterials)（の古いバージョン）を元にしている．
入出力部分，エラーメッセージは[ocaml/ocaml](https://github.com/ocaml/ocaml)を参考にしている．

## 実装したもの
- 関数（再帰関数を含む），リスト，ヴァリアント（再帰が可能），参照
- パターンマッチング（変数の使用，ネストが可能）
- 型推論（let多相，value restriction）
- 丁寧なエラーメッセージ（エラー箇所の表示）

## 使い方
事前にduneをインストールしておく必要がある．

1. `git clone https://github.com/samosica/miniml_interpreter.git`
2. `cd miniml_interpreter`
3. `dune exec miniml`でインタプリタが起動する．`dune exec miniml x.ml`とすると，`x.ml`の中身が実行される．一方で，`dune exec miniml < x.ml`は正しく動作しないことがある🤔．

## 使用例
[AtCoder Beginner Contest 138 F - Coincidence](https://atcoder.jp/contests/abc138/tasks/abc138_f)を解くコードが次のように書ける．
ただし，入出力は実装していないので，ロジック部分だけを書いている．また，リンク先の入出力例だけしか試していない．

```ocaml
let eqn n m = (-1) < n + (-1) * m && n + (-1) * m < 1 ;;

(* tuple *)
type ('a, 'b) pair = Pair of 'a * 'b ;;
type ('a, 'b, 'c) triple = Triple of 'a * 'b * 'c ;;
type ('a, 'b, 'c, 'd) quad = Quad of 'a * 'b * 'c * 'd ;;

let fst p =
  match p with
    Pair(f, _) -> f
let snd p =
  match p with
    Pair(_, s) -> s ;;

(* list *)
let rec mem = fun x -> fun l ->
  match l with
    [] -> false
  | y :: l -> eqn x y || mem x l ;;

let rec fold_left = fun f -> fun acc -> fun l ->
  match l with
    [] -> acc
  | x :: l -> fold_left f (f acc x) l ;;

let rec for_all2 = fun p -> fun l -> fun l' ->
  match Pair(l, l') with
    Pair([], []) -> true
  | Pair(x :: l, y :: l') -> p x y && for_all2 p l l'
  | _ -> false ;;

let rec map2 = fun f -> fun l -> fun l' ->
  match Pair(l, l') with
    Pair([], []) -> []
  | Pair(x :: l, y :: l') -> f x y :: map2 f l l'
  | _ -> [] ;;

(* tree *)
(* 配列がないので葉に参照を持たせた2分木で代用している *)
type 'a tree = B of 'a tree * 'a tree
             | L of 'a ref ;;

let rec make_tree = fun d ->
  if d < 1 then L (ref (-1)) else B(make_tree (d + (-1)), make_tree (d + (-1))) ;;

let make_tree d = Pair(d, make_tree d) ;;

let at k t =
  let d = fst t in
  let t = snd t in
  let rec at' = fun l -> fun t ->
    match t with
      B(lt, rt) -> if eqn ((k lsr (l + (-1))) land 1) 0
                   then at' (l + (-1)) lt
                   else at' (l + (-1)) rt
    | L r -> r in
  at' d t ;;

let set k v t = at k t := v
let get k t = !(at k t) ;;

(* ---------------------------------------- *)

(* automaton *)
type 'a automaton = Automaton of ('a -> int -> int) * (int -> bool) ;;

let transition a =
  match a with
    Automaton(d, _) -> d
let is_accepted a =
  match a with
    Automaton(_, p) -> p ;; 

let make_automaton d acs =
  Automaton (d, fun s -> mem s acs) ;;

let a1 =
  let d q s =
    match q with
      Quad(x, y, l, r) ->
       (match Triple(x, y, s) with
          Triple(1, 0, 0) -> 1
        | Triple(0, 1, 0) -> 1
        | Triple(1, 1, 0) -> 2
        | Triple(_, _, _) -> s) in
  let acs = [0; 2] in
  make_automaton d acs ;;
  
let a2 =
  let d q s =
    match q with
      Quad(x, y, l, r) ->
       (match Triple(x, l, s) with
          Triple(1, 0, 0) -> 1
        | Triple(0, 1, 0) -> 2
        | Triple(_, _, _) -> s) in
  let acs = [0; 1] in
  make_automaton d acs ;;

let a3 =
  let d q s =
    match q with
      Quad(x, y, l, r) ->
       (match Triple(y, r, s) with
          Triple(1, 0, 0) -> 1
        | Triple(0, 1, 0) -> 2
        | Triple(_, _, _) -> s) in
  let acs = [0; 2] in
  make_automaton d acs ;;  

let a4 =
  let d q s =
    match q with
      Quad(x, y, l, r) ->
       (match Triple(x, y, s) with
          Triple(1, 0, 0) -> 1
        | Triple(_, _, _) -> s) in
  let acs = [0] in
  make_automaton d acs ;;

let aus = [a1; a2; a3; a4] ;;

let mo = 1000000007 ;;

let solve l r =
  let t = make_tree 13 in (* 2^13 > 60 * 81 *)
  let rec f = fun i -> fun ss ->
    let j = fold_left (fun x y -> x * 3 + y) 0 ss in
    if i < 0
    then if for_all2 (fun s au -> is_accepted au s) ss aus
         then 1
         else 0
    else if eqn (get (i * 81 + j) t) (-1)
    then (let v = fold_left (fun s p ->
                      let a = fst p in
                      let b = snd p in
                      let ss = map2 (fun s au -> (transition au) (Quad(a, b, (l lsr i) land 1, (r lsr i) land 1)) s) ss aus in
                     (s + f (i + (-1)) ss) mod mo) 0 [Pair(0, 0); Pair(0, 1); Pair(1, 0); Pair(1, 1)] in
          let tmp = set (i * 81 + j) v t in
          v)
    else get (i * 81 + j) t in
  f 59 [0; 0; 0; 0] ;;

(* リンク先の入力例に対する出力 *)
let out1 = solve 2 3
let out2 = solve 10 100
let out3 = solve 1 1000000000000000000 ;;
```

