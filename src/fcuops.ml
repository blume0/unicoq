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

open EConstr
module C = Constr
module CND = Context.Named.Declaration

let (let*) = Option.bind
let return x = Some x
let fail() = None

module X = struct
      type t = C.constr
      let compare = C.compare
end
module TMap = CMap.Make(X)

let rec xfold f acc t =
  let acc = f acc t in
  C.fold (fun acc t -> xfold f acc t) acc t



let is_constructor_like_head sigma t = match kind sigma t with
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
let rec is_restricted sigma t = match kind sigma t with
  | Rel _  | Var _ | Sort _ -> true
  | Meta _ | Evar _ -> false
  | Lambda _ | LetIn _ | Prod _ -> false
  | Cast (t, _, _ (* TODO: ? *)) -> is_restricted sigma t
  | App (t, args) ->
     (* TODO: see if the invariants that t is non-applicative and |args| > 0
        is always respected                                               *)
     not (Array.exists (fun a -> not@@ is_restricted sigma a) args)
     && is_constructor_like_head sigma t
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
     pruning procedure                                                            *)


let check_term_restriction sigma args =
  not @@ List.exists (fun t -> not (is_restricted sigma t)) args

type evar_argument =
  | Evarg_Rel of int
  | Evarg_Name of Names.Id.t

(* In addition to the above description of the local-restriction condition, there are two
   additional relaxings controlled by the 'strict' argument in the following implementation,
   to make it correspond to the way the HOPU variable restriction check is actually conducted
   in Ziliani-Sozeau's Unicoq implementation:
   1- Non-restricted-term argument are just ignored
   2- Non-unique arguments are allowed at this point, are provoke a failure to apply the rule
      only in the case they are actually needed.

      TODO: Just realized I am not doing the local restriction check at all here i am just
      checking for syntactical equality not structural occurence am stupid
*)
let check_local_restriction ?(strict=false) sigma subst ctx args =
  let allargs = subst@args in
  let no_subterm_occ t =
    let occs = xfold
      (fun occs t ->
        occs +
        CList.count
          (fun t' -> C.compare t (to_constr sigma t') = 0) allargs)
      0 t
    in
    let _ = assert (occs <> 0) in occs = 1
  in
  let check_subst acc t decl =
    let* map = acc in
    if not@@ is_restricted sigma t then if strict then fail() else acc else
    let t = to_constr sigma t in
    if no_subterm_occ t then
      let var = Evarg_Name (CND.get_id decl) in
      return (TMap.add t (Some var) map)
    else if strict then fail() else return (TMap.add t None map)
  in let check_args i acc t =
    let* map = acc in
    if not@@ is_restricted sigma t then if strict then fail() else acc else
    let t = to_constr sigma t in
    if no_subterm_occ t then
      return (TMap.add t (Some(Evarg_Rel i)) map)
    else if strict then fail() else return (TMap.add t None map)
  in
  let map = List.fold_left2 check_subst (return TMap.empty) subst ctx in
  CList.fold_left_i check_args 1 map args


(* precondition: is_restricted sigma t *)
let rec unlift_restricted sigma i t =
  match EConstr.kind sigma t with
  | Rel j ->
     (* TODO: make sure DeBrujin indices start at 1 *)
     if j > i then return (mkRel (j-i))
     else fail()
  | _ ->
     let exception MyExit in
     begin try
         return @@
         map_with_binders
            sigma failwith
            (fun _ t -> match unlift_restricted sigma i t with
                        | Some x -> x | None -> raise MyExit)
            "term was not restricted" t
     with MyExit -> fail() end

(* Same interface as the original invert *)
(* Inverting
       ?x[subs] args = t where (sigma ⊧ ?x[ctx]) *)
let invert prune_map sigma ctx t subs args x =
  let exception MyExit in
  let prune_map = ref prune_map in

  (*DEBUG*)
  let ppt c = Constr.debug_print (EConstr.Unsafe.to_constr c) in
  begin let open Pp in
  Format.printf "BLUME: REVERTING ?%a@." pp_with @@
    (Option.default (Names.Id.of_string("U"^(string_of_int (Evar.repr x)))) (Evd.evar_ident x sigma)
     |> Names.Id.print)
    ++ (str"[") ++ prlist_with_sep (fun _ -> str"; ") ppt subs
    ++ (str"] ") ++ prlist_with_sep (fun _ -> str" ") ppt args
    ++ (str " ?R? ") ++ (ppt t)
  end;

  let subsargs = subs@args in
  if not@@ check_term_restriction sigma subsargs then fail() else
  let* evar_args_map = check_local_restriction sigma subs ctx (List.rev args) in

  Format.printf "BLUME: MAP IS %a@." Pp.pp_with
  (TMap.fold_left (fun t a acc ->
       let open Pp in let hehe = match a with
                      | Some (Evarg_Name(n)) -> Names.Id.print n
                      | Some (Evarg_Rel(n)) -> int n
                      | None -> str"BAD"
                      in acc ++ (C.debug_print t ++ str":" ++ hehe) ++ str", "
     ) evar_args_map (Pp.str""));

  let rec invert' inside_evar t i =
    if is_restricted sigma t then
      let _ = Format.printf "INVERTING RESTRICTED %a@." Pp.pp_with (ppt t) in
      let* et = unlift_restricted sigma i t in
      let t = to_constr sigma et in
      match TMap.find_opt t evar_args_map with
        (* TODO: check indice stuff *)
      | Some (Some(Evarg_Rel j)) -> return (mkRel (j+i))
      | Some (Some(Evarg_Name n)) -> return (mkVar n)
      | Some None -> fail()
      | None ->
         (* Here the term does not occur as an argument, but we can still
            try to invert its subterms. *)
         begin
           try return (map_with_binders sigma succ (fun i t ->
                           match invert' inside_evar t i with
                           | Some t -> t
                           | None -> raise MyExit) i et)
           with MyExit -> fail()
         end

    else match kind sigma t with
    | Evar (y, _) when Evar.equal x y -> fail()
    | Evar (y, y_args) ->
      begin
        let y_args = Evd.expand_existential sigma (y, y_args) in
        let invert_or_prune pos u =
          match invert' true u i with
          | Some u -> u
          | None ->
             if not inside_evar then begin
                 prune_map := Evar.Map.update y
                   (fun l -> match l with
                             | Some l -> Some (pos::l)
                             | None -> Some [pos]) !prune_map;
                 u
             end else raise MyExit
        in
        try return (mkLEvar sigma (y, List.mapi invert_or_prune y_args))
        with MyExit -> fail()
      end

    | _ ->
       try return (map_with_binders sigma succ (fun i c ->
                       match invert' inside_evar c i with
                       | Some c -> c
                       | None -> raise MyExit) i t)
       with MyExit -> fail()
  in
  let* t_minus_one = invert' false t 0 in
  (*DEBUG*)
  begin let open Pp in
    Format.printf "BLUME: SUCCESSFULLY REVERTED AS %a@." pp_with
    (ppt t_minus_one)
  end;
  return (!prune_map, t_minus_one)


