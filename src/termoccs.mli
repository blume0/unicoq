(*************************************************************************)
(* Unicoq + Function as Constructors Unification experimentation         *)
(* 2025 - Wassim Ait-Moussa <d.w.aitmoussa@gmail.com>                    *)
(*                                                                       *)
(* This file is a trial at a generic interface supposed to offer some kind
   of generic fast lookup for some subterm of a term
   The purpose is to have, given a list S of terms and some term t,
   a way of enumerating every pair (s, t{t'}) that satisfies t' = s

   - Inorder for this operation to be "linear" in the sizes of t and S, it is
   (to my current understanding) necessary to have a constant time comparing
   operation between subterms of t and elements of S.
   - To achieve this, all the involved terms are "pre-coocked" by annotating
   each node of their tree strcuture with its hash : thus (modulo collisions)
   different terms can be compared by only looking at their head.

   TODO: this looks like a common operation, I should look at how close it is
   in spirit to hashconsing, and most importantly, I should try to look
   for solutions to this specific "subtree occurence" problem in the
   literature because it does look like a reasonably general one?
*)
(*************************************************************************)



type t

val hash : Constr.t -> t
val to_constr : t -> Constr.t
val compare : t -> t -> int

val kind :  t -> (t, t, Sorts.t, UVars.Instance.t, Sorts.relevance)
                 Constr.kind_of_term

module Set : CSig.SetS with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set

val xfold : ('a -> t -> 'a) -> 'a -> t -> 'a

val map_with_binders :
  ('a -> 'a) -> ('a -> t -> t) -> 'a -> t -> t
