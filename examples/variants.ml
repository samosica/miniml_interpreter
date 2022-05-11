type nat = S of nat
         | O ;;

let two = S (S O)
let three = S two
let four = S three ;;

let rec int_of_nat = fun n ->
  match n with
    S n -> 1 + int_of_nat n
  | _ -> 0 ;;

let rec addn = fun n -> fun m ->
  match n with
    S n -> S (addn n m)
  | _ -> m ;;

let rec muln = fun n -> fun m ->
  match n with
    S n -> addn m (muln n m)
  | _ -> O ;;

int_of_nat two ;;
addn three four ;;
muln three four ;;

type 'a mylist = Cons of 'a * 'a mylist
               | Nil ;;

let rec adj_diff = fun l ->
  match l with
    Nil -> Nil
  | Cons(_, Nil) -> Nil
  | Cons(x, Cons(y, z)) -> Cons(y + (-1) * x, adj_diff (Cons(y, z))) ;;

adj_diff (Cons(1, Cons(3, Cons(4, Cons(2, Nil))))) ;;
