let intersect s1 s2 =
  List.fold_right
    (fun x l -> if List.mem x s2
                then x :: l
                else l) s1 []

(* compatible with List.assoc_opt *)
let assoc_opt x l =
  try
    Some (List.assoc x l)
  with
    Not_found -> None

(* l で重複しているキー（第1要素）を持つ組を削除する．
 * それぞれのキーに対して，そのキーを持つ最後の組が残る．
 *)
let nubLast l =
  List.fold_right (fun ((k, _) as p) res ->
      if List.mem_assoc k res
      then res
      else p :: res) l []

(* リスト内の最初の重複する要素を返す *)
let rec firstDuplicate = function
    [] -> None
  | x :: l when List.mem x l -> Some x
  | _ :: l -> firstDuplicate l

(* 組のリスト内の最初の重複するキーを返す *)
let firstDuplicateKey l = List.map (fun (k, _) -> k) l
                          |> firstDuplicate

(* 3つ組のリスト内の最初の重複するキーを返す *)
let firstDuplicateKey3 l = List.map (fun (k, _, _) -> k) l
                           |> firstDuplicate
