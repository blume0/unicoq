(*************************************************************************)
(* Unicoq + Function as Constructors Unification experimentation         *)
(* 2025 - Wassim Ait-Moussa <d.w.aitmoussa@gmail.com>                    *)
(*                                                                       *)
(* I try to have a first working implementation here, not necessarily in
   the most efficient way still without a full grasp of the utilities
   exposed by the kernel and engine APIs (in particular, there might be
   some redundant things here                                            *)
(* I have also not formalized what I am doing yet, so what is here is
   only to play around and get some intuition about the problem and the
   choices that can be made                                              *)
(*************************************************************************)


module C = Constr

let is_constructor_like_head t = match C.kind t with
  | Rel _ | Var _ | Ind _ -> true
  | Construct _ -> true (* TODO: but it is invertible *)
  | Const _ -> true (* TODO: ignoring delta-reductions *)
  | _ -> false


(* For now, the only accepted form for a restricted term is f u₁...uₖ where
   the uᵢs are restricted (and k>0) and f is either a variable,
   a constructor, a type constructor or a constant.
   - The inclusion of constructors and constants as valid heads is
     questionable, as they can reduce and aren't really "neutral"
   - On the other hand, if the above is valid, I think there might be
     a way to also add case constructs ?
   I think I need to think more about the essence/the points of the FCU
   restriction in the simple λ-calculus to see how it extends to the
   inductive part of the CIC.                                             *)
let rec is_restricted t = match C.kind t with
  | Rel _ | Var _ | Sort _ -> true
  | Meta _ | Evar _ -> false
  | Lambda _ | LetIn _ | Prod _ -> false
  | Cast (t, _, _ (* TODO: ? *)) -> is_restricted t
  | App (t, args) ->
     (* TODO: see if the invariants that t is non-applicative and |args| > 0
        is always respected                                               *)
     not@@ Array.exists is_restricted args
     && is_constructor_like_head t
  | Const _ | Ind _ | Construct _ -> false
  | Case _ -> false
      (* TODO: maybe there is something to do with this ? *)
  | Fix _ | CoFix _ -> false
  | Proj _ -> false
  | Int _ | Float _ | String _ | Array _ -> false

