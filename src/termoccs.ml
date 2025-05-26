open Constr
open Hashset.Combine
open Names
open UVars

type 'a annotated_term = {
  kind : ('a annotated_term,'a annotated_term,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term;
  hash : 'a;
}

type t = int annotated_term

let mk c h = {kind=c;hash=h}


(* Copy of Constr.hash except every term is annotated with its hash *)
let rec hash t =
  match kind t with
    | Var i -> mk (Var i) (combinesmall 1 (Id.hash i))
    | Sort s -> mk (Sort s) (combinesmall 2 (Sorts.hash s))
    | Cast (c, k, t) ->
      let {hash=hc; _} as c = hash c in
      let {hash=ht; _} as t = hash t in
      let h = combinesmall 3 (combine3 hc (hash_cast_kind k) ht) in
      mk (Cast (c, k, t)) h
    | Prod (x, t, c) ->
       let {hash=hc;_} as c = hash c in
       let {hash=ht;_} as t = hash t in
       mk (Prod (x,t,c)) (combinesmall 4 (combine ht hc))
    | Lambda (x, t, c) ->
       let {hash=hc;_} as c = hash c in
       let {hash=ht;_} as t = hash t in
       mk (Lambda (x,t,c)) (combinesmall 5 (combine ht hc))
    | LetIn (x, b, t, c) ->
       let {hash=hc;_} as c = hash c in
       let {hash=ht;_} as t = hash t in
       let {hash=hb;_} as b = hash b in
       mk (LetIn (x,b,t,c)) (combinesmall 6 (combine3 hb ht hc))
    | App (c,l) -> begin match kind c with
        | Cast (c, _, _) -> hash (mkApp (c,l)) (* WTF *)
        | _ ->
           let {hash=hc;_} as c = hash c in
           let (hl, l) = hash_term_array l in
           mk (App (c, l)) (combinesmall 7 (combine hl hc))
      end
    | Evar (e,l) ->
       let (hl,l) = (hash_term_list l) in
       mk (Evar (e,l)) (combinesmall 8 (combine (Evar.hash e) hl))
    | Const (c,u) ->
       mk (Const (c,u)) @@
         combinesmall 9 (combine (Constant.CanOrd.hash c) (Instance.hash u))
    | Ind (ind,u) ->
       mk (Ind (ind, u)) @@
         combinesmall 10 (combine (Ind.CanOrd.hash ind) (Instance.hash u))
    | Construct (c,u) ->
       mk (Construct (c,u)) @@
         combinesmall 11 (combine (Construct.CanOrd.hash c) (Instance.hash u))
    | Case (x , u, pms, (p,r), iv, c, bl) ->
       let {hash=hc;_} as c = hash c in
       let (hiv, iv) = hash_invert iv in
       let (hpms, pms) = hash_term_array pms in
       let (hp, p) = hash_under_context p in
       let (hbl, bl) = hash_branches bl in
       mk (Case(x,u,pms,(p,r),iv,c,bl)) @@
         combinesmall 12 (combine5 hc hiv hpms (Instance.hash u)
                         (combine3 hp (Sorts.relevance_hash r) hbl))
    | Fix (x ,(y, tl, bl)) ->
       let (hbl, bl) = (hash_term_array bl) in
       let (htl, tl) = (hash_term_array tl) in
       mk (Fix(x,(y,tl,bl))) (combinesmall 13 (combine hbl htl))
    | CoFix(x, (y, tl, bl)) ->
       let (hbl, bl) = (hash_term_array bl) in
       let (htl, tl) = (hash_term_array tl) in
       mk (CoFix(x,(y,tl,bl))) (combinesmall 14 (combine hbl htl))
    | Meta n -> mk (Meta n) (combinesmall 15 n)
    | Rel n -> mk (Rel n) (combinesmall 16 n)
    | Proj (p,r, c) ->
      let {hash=hc;_} as c = hash c in
      mk (Proj(p,r,c)) @@
        combinesmall 17 (combine3 (Projection.CanOrd.hash p)
                           (Sorts.relevance_hash r) hc)
    | Int i -> mk (Int i) (combinesmall 18 (Uint63.hash i))
    | Float f -> mk (Float f) (combinesmall 19 (Float64.hash f))
    | String s -> mk (String s) (combinesmall 20 (Pstring.hash s))
    | Array(u,t,def,ty) ->
       let (ht, t) = hash_term_array t in
       let {hash=hty;_} as ty = hash ty in
       let {hash=hdef;_} as def = hash def in
       mk (Array(u,t,def,ty)) @@
         combinesmall 21 (combine4 (Instance.hash u) ht hdef hty)

and hash_invert = function
  | NoInvert -> (0, NoInvert)
  | CaseInvert {indices;}  ->
     let (hindices, indices) = hash_term_array indices in
     (combinesmall 1 hindices, CaseInvert {indices})

and hash_term_array t =
  let (ht, t) = Array.fold_left_map (fun acc t ->
      let {hash=ht;_} as t = hash t in
      (combine acc ht, t))
    0 t in
  (ht, t)

and hash_term_list t =
  let t = SList.Skip.map hash t in
  let ht = SList.Skip.fold (fun acc t -> combine (t.hash) acc) 0 t in
  (ht, t)

and hash_under_context (x, t) =
  let {hash=ht;_} as t = hash t in
  (ht, (x, t))

and hash_branches bl =
  let hashes, bl = Array.split@@ (Array.map hash_under_context bl) in
  let hbl = Array.fold_left (fun acc n -> combine acc n) 0 hashes in
  (hbl, bl)



let kind t = t.kind


let rec to_constr t = Constr.of_kind (to_constr_aux t)

(* TODO?: generic polymorphic kind_to_term map operation *)
and to_constr_aux t : (constr,constr,_,_,_) kind_of_term =
  match t.kind with
  | Var n -> Var n
  | Rel i -> Rel i
  | Sort s -> Sort s
  | Cast (c, k, t) -> Cast (to_constr c, k, to_constr t)
  | Prod (x, t, c) -> Prod (x, to_constr t, to_constr c)
  | Lambda (x, t, c) -> Lambda (x, to_constr t, to_constr c)
  | LetIn (x, b, t, c) -> LetIn (x, to_constr b, to_constr t, to_constr c)
  | App (c, l) -> App(to_constr c, Array.map to_constr l)
  | Evar (e, l) -> Evar(e, SList.Skip.map to_constr l)
  | Const (c, u) -> Const(c, u)
  | Ind (ind, u) -> Ind (ind, u)
  | Construct (c,u) -> Construct (c,u)
  | Case(x,u,pms,((y,p),r), iv, c, bl) -> Case(x, u,
      Array.map to_constr pms,
      ((y,to_constr p),r),
      to_constr_invert iv,
      to_constr c,
      to_constr_branches bl
    )
  | Fix (x, (y, tl, bl)) ->
     Fix(x,(y,Array.map to_constr tl,Array.map to_constr bl))
  | CoFix (x, (y, tl, bl)) ->
     CoFix(x,(y,Array.map to_constr tl,Array.map to_constr bl))
  | Meta n -> Meta n
  | Proj (p,r,c) -> Proj (p, r, to_constr c)
  | Int i -> Int i | String s -> String s | Float f -> Float f
  | Array (u,t,def,ty) ->
     Array(u, Array.map to_constr t, to_constr def, to_constr ty)

and to_constr_invert = function
    | NoInvert -> NoInvert
    | CaseInvert{indices;} -> CaseInvert{indices=Array.map to_constr indices}

and to_constr_branches bl =
  Array.map (fun (x,t) -> (x, to_constr t)) bl


let compare t t' =
  if t.hash = t'.hash then (* in the case of a collision, check equality *)
    Constr.compare (to_constr t) (to_constr t')
  else t.hash - t'.hash

module Order = struct
     type nonrec t = t
     let compare = compare
end
module Set = CSet.Make(Order)
module Map = CMap.Make(Order)


let fold_invert f acc = function
  | NoInvert -> acc
  | CaseInvert {indices} ->
    Array.fold_left f acc indices

let fold f acc c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Proj (_p,_r,c) -> f acc c
  | Evar (_,l) -> SList.Skip.fold f acc l
  | Case (_,_,pms,((_,p),_),iv,c,bl) ->
    Array.fold_left (fun acc (_, b) -> f acc b) (f (fold_invert f (f (Array.fold_left f acc pms) p) iv) c) bl
  | Fix (_,(_lna,tl,bl)) ->
    CArray.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | CoFix (_,(_lna,tl,bl)) ->
    CArray.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | Array(_u,t,def,ty) ->
    f (f (Array.fold_left f acc t) def) ty

let rec xfold f acc c =
  let acc = f acc c in
  fold (fun acc c -> xfold f acc c) acc c


