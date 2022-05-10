type 'a t

exception Not_allocated

val make : unit -> 'a t
val allocate : 'a -> 'a t -> int
val lookup : int -> 'a t -> 'a
val update : int -> 'a -> 'a t -> unit
