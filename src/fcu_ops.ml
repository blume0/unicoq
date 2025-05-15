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


(* In the pure Functions as Constructors algorithm, there are three
   restrictions on the system:
   - The term restriction: Every argument tᵢ in an evar's spine [?X t₁...tₙ]
     satisfies that every node is either a function symbol (in the sense of
     a fixed signature in the simple lmabda calculus) or a bound variable,
     and every leaf is a bound variable.
   - The local restriction: Given any evar instance [?X t₁...tₙ] in the
     system and i≠j, we have that tᵢ ⊈ tⱼ.
   - The global restriction: Given any two occurences [?X t₁...tₙ] and
     [?Y u₁...uₘ] in the same equation of a system, we have tᵢ ⊄ uᵢ.

   In our case, since we are not working in a pure system of equations
   (i.e there are other rules/heuristics that do not commute with the
   HOPU algorithm), we should be only concerned on the subset of these
   conditions that allows the Meta-Inst rule to work (~~ be sound + locally
   complete in some restricted sense ?)
   It is my (unproven) understanding that these rules need only be enforced
   on the head r.h.s mvar in the rule. Precisely, given an equaition of the
   form [?X t₁ ... tₙ = s], one must check that:
   - Term restriction: for the argumnets of ?X only.
   - Local restriction: for the arguments of ?X only.
   - Global retrcition: for each occurence [?Y u₁ ... uₘ] in s,
     only check that tᵢ ⊄ uⱼ.
     --> to my understanding, this only guarantees the completeness of the
     pruning procedure
*)


module X = struct
      type t = C.constr
      let compare = C.compare
end
module TMap = CMap.Make(X)

module CND = Context.Named.Declaration

let (let*) a f = match a with None -> None | Some a -> f a
let return x = Some x
let fail() = None

let check_term_restriction args =
  not @@ List.exists (fun t -> not (is_restricted t)) args

type evar_argument =
  | Evarg_Rel of int
  | Evarg_Name of Names.Id.t

let lift_evar_argument i = function
  | Evarg_Name _ as x -> x
  | Evarg_Rel j -> Evarg_Rel (j + i)

let check_local_restriction subst ctx args =
  let check_subst acc t decl =
    let* map = acc in
    match TMap.find_opt t map with
    | None ->
       let var = Evarg_Name (CND.get_id decl) in
       return (TMap.add t var map)
    | Some _ -> fail()
  in let check_args i acc t =
    let* map = acc in
    match TMap.find_opt t map with
    | None -> return @@ TMap.add t (Evarg_Rel i) map
    | Some _ -> fail()
  in
  let map = List.fold_left2 check_subst (return TMap.empty) subst ctx in
  CList.fold_left_i check_args 1 map args


(* Same interface as the original invert *)
let invert prune_map sigma ctx t subs args ev =
  failwith "Yepp"
  (* TODO: handle de brujin things *)
