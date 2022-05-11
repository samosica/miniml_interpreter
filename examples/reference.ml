let fact n =
  let r = ref 1 in
  let rec f = fun n ->
    if n < 1
    then ()
    else (r := !r * n; f (n + (-1))) in
  f n; !r ;;

fact 10 ;;
