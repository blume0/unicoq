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

let _ = xfold


let is_constructor_like_head kind t = match kind t with
  | C.Rel _ | Var _ | Ind _ -> true
  | Construct _ -> true (* TODO: but it is invertible *)
  | Const _ ->
     (* (?X[f x] = f x) with (f := fun x => (x, x)) ∈ E
        (?X:=fun e => e) is not an mgu
        Example of incompatible solution: (?X:=fun e => (e.2, e.2)
     *)
     false
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
let rec is_restricted kind ?(i=0) t = match kind t with
  | C.Var n  -> true
  | Rel j -> j > i
  | Meta _ | Evar _ -> false
  | Lambda _ | LetIn _ | Prod _ -> false
  | Cast (t, _, bigt (* TODO: is it necessary ? *)) ->
    is_restricted kind t && is_restricted kind bigt
  | App (t, args) ->
     (* TODO: see if the invariants that t is non-applicative and |args| > 0
        is always respected                                               *)
     not (Array.exists (fun a -> not@@ is_restricted ~i kind a) args)
     && is_constructor_like_head kind t
  | Const _ | Ind _ | Construct _ | Sort _ -> false
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
  not @@ List.exists (fun t -> not (is_restricted (kind sigma) t)) args

type evar_argument =
  | Evarg_Rel of int
  | Evarg_Name of Names.Id.t


(* Counts the size of { t' | t' occurence in t /\ t' ∈ args }
   TODO: quadratic in the worst case ?                                *)
let count_subterm_occ strict xfold fold compare t args =
  let fold_square =
    xfold
      (fun occs t -> occs + CList.count (fun t' -> compare t t' = 0) args)
  in
  if strict then
    fold fold_square 0 t
  else fold_square 0 t

(* In addition to the above description of the local-restriction condition, there are two
   additional relaxings controlled by the 'strict' argument in the following implementation,
   to make it correspond to the way the HOPU variable restriction check is actually conducted
   in Ziliani-Sozeau's Unicoq implementation:
   1- Non-restricted-term arguments are just ignored
   2- Non-unique arguments are allowed at this point, are provoke a failure
      to apply the rule only in the case they are actually needed.
*)


let check_occ_restriction ?(strict=false) ?(expected=0) ?(map=TMap.empty)
                          sigma subst ctx args ts =
  let hkind = Termoccs.kind in
  let canonize t = to_constr sigma t |> Termoccs.hash in
  let to_constr = Termoccs.to_constr in
  let count_fun = Termoccs.(count_subterm_occ strict xfold fold compare) in

  let allargs = List.map canonize ts in
  let subst = List.map canonize subst in
  let args = List.map canonize args in

  let check_subst acc t decl =
    let* map = acc in
    if not@@ is_restricted hkind t then acc else
    if count_fun t allargs = expected then
      let var = Evarg_Name (CND.get_id decl) in
      return
        (TMap.update (to_constr t)
           (function None->Some(Some(var))|Some(x)->Some(x)) map)
    else return (TMap.add (to_constr t) None map)
  in let check_args i acc t =
    let* map = acc in
    if not@@ is_restricted hkind t then acc else
    if count_fun t allargs = expected then
      return (TMap.update (to_constr t)
             (function None->(Some(Some(Evarg_Rel i)))|Some(x)->Some(x)) map)
    else return (TMap.add (to_constr t) None map)
  in
  let map = List.fold_left2 check_subst (return map) subst ctx in
  CList.fold_left_i check_args 1 map args

let check_local_restriction sigma subst ctx args =
  let ts = subst@args in
  check_occ_restriction ~expected:1 sigma subst ctx args ts

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

let rec collect_evar_args sigma i acc t =
  match C.kind t with
  | Evar(y, y_args) ->
     let y_args = Evd.expand_existential sigma
                    (y, SList.Skip.map of_constr y_args) in
     let y_args = List.filter (is_restricted (kind sigma) ~i) y_args in
     let y_args = List.map (unlift_restricted sigma i) y_args in
     CList.map Option.get (CList.filter ((<>) None) y_args) @ acc
  | _ -> C.fold_constr_with_binders succ (collect_evar_args sigma) i acc t


let check_global_restriction sigma map subst ctx args t =
  let t = to_constr ~abort_on_undefined_evars:false sigma t in
  let ts = collect_evar_args sigma 0 [] t in
  let ts = List.filter (is_restricted (kind sigma)) ts in
  check_occ_restriction ~strict:true ~map sigma subst ctx args ts

(* Same interface as the original invert *)
(* Inverting
       ?x[subs] args = t where (sigma ⊧ ?x[ctx]) *)
let invert prune_map sigma ctx t subs args x =
  let exception MyExit in
  let prune_map = ref prune_map in

  (* DEBUG *)
  (* let ppe e = *)
  (*   Printer.pr_existential_key Environ.empty_env sigma x *)
  (* in *)
  (* let ppt c = Printer.pr_econstr_env Environ.empty_env sigma c in *)
  (* begin let open Pp in *)
  (* Format.printf "BLUME: REVERTING %a@." pp_with @@ *)
  (*   ppe x *)
  (*   ++ (str"[") ++ prlist_with_sep (fun _ -> str"; ") ppt subs *)
  (*   ++ (str"] ") ++ prlist_with_sep (fun _ -> str" ") ppt args *)
  (*   ++ (str " ?R? ") ++ (ppt t) *)
  (* end; *)
  (* let _ = ppt in *)

  let subsargs = subs@args in
  if not@@ check_term_restriction sigma subsargs then fail() else
  let args = List.rev args in
  let* evar_args_map =
    check_local_restriction sigma subs ctx args
  in
  let* evar_args_map =
    check_global_restriction sigma evar_args_map subs ctx args t
  in

  let rec invert' inside_evar t (unlift, i) =
    (* let _ = Format.printf "INVERT' OF %a (i=%d, unlift=%b,restricted=%b)@." *)
    (*     Pp.pp_with (ppt t) i *)
    (*     unlift *)
    (*     @@ let i = if unlift then i else 0 in is_restricted (kind sigma) ~i t *)
    (* in *)
    if is_restricted (kind sigma) ~i:(if unlift then i else 0) t then
      (* let _ = Format.printf "INVERTING RESTRICTED(%d) %a@." i Pp.pp_with (ppt t) in *)
      let* et = if unlift then unlift_restricted sigma i t else return t in
      let t = to_constr sigma et in
      match TMap.find_opt t evar_args_map with
        (* TODO: check indice stuff *)
      | Some (Some(Evarg_Rel j)) -> return (mkRel (j+i))
      | Some (Some(Evarg_Name n)) -> return (mkVar n)
      | Some None -> raise MyExit
      | None ->
         (* Here the term does not occur as an argument, but we can still
            try to invert its subterms. *)
         begin
           match C.kind t with
           (* if we're a leaf (i.e. a bound variable), it is over *)
           | Rel _ | Var _ -> fail() | _ ->
           let succ _ = failwith "Term was not restricted" in
           try return (map_with_binders sigma succ (fun _ t ->
                           match invert' inside_evar t (false,i) with
                           | Some t -> t
                           | None -> raise MyExit) (false,-1) et)
           with MyExit -> fail()
         end

    else match kind sigma t with
    | Evar (y, _) when Evar.equal x y -> fail()
    | Evar (y, y_args) ->
      begin
        let y_args = Evd.expand_existential sigma (y, y_args) in
        let invert_or_prune pos u =
          match invert' true u (unlift, i) with
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
       let succ (_, i) = (true, succ i) in
       try return (map_with_binders sigma succ (fun (u,i) c ->
                       match invert' inside_evar c (u,i) with
                       | Some c -> c
                       | None -> raise MyExit) (unlift,i) t)
       with MyExit -> fail()
  in
  let* t_minus_one = try invert' false t (false,0) with MyExit -> fail() in
  (*DEBUG*)
  (* begin let open Pp in *)
  (*   Format.printf "BLUME: SUCCESSFULLY REVERTED AS %a@." pp_with *)
  (*   (ppt t_minus_one) *)
  (* end; *)
  return (!prune_map, t_minus_one)


