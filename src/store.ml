type 'a tree =
  B of 'a tree * 'a * 'a tree
| L

type 'a t = ('a tree * int) ref

exception Not_allocated

let path n =
  let rec path' = function
      0 | 1 -> []
    | n when n mod 2 = 0 -> 0 :: path' (n / 2)
    | n -> 1 :: path' (n / 2)
  in List.rev (path' n)

let make () = ref (L, 0)

let allocate x s =
  let rec allocate' t p =
    match t, p with
      _, [] -> B(L, x, L)
    | L, _ -> B(L, x, L) (* exhaustive check で引っかからないように冗長に書いている *)
    | B(lt, y, rt), 0 :: p -> B(allocate' lt p, y, rt)
    | B(lt, y, rt), _ :: p -> B(lt, y, allocate' rt p) in
  let (t, n) = !s in
  s := (allocate' t (path (n + 1)), n + 1); n + 1

let lookup k s =
  let rec lookup' t p =
    match t, p with
      L, _ -> raise Not_allocated
    | B(_, x, _), [] -> x
    | B(lt, _, _), 0 :: p -> lookup' lt p
    | B(_, _, rt), _ :: p -> lookup' rt p in
  let (t, _) = !s in
  lookup' t (path k)

let update k v s =
  let rec update' t p =
    match t, p with
      L, _ -> raise Not_allocated
    | B(lt, _, rt), [] -> B(lt, v, rt)
    | B(lt, w, rt), 0 :: p -> B(update' lt p, w, rt)
    | B(lt, w, rt), _ :: p -> B(lt, w, update' rt p) in
  let (t, n) = !s in
  s := (update' t (path k), n)
