
val inst_constr_as_const : bool ref
val inst_defn_as_const : bool ref
val inst_gconst_as_restricted : bool ref
val inst_local_cond_heuristic : bool ref
val debug : bool ref

val invert :
  Environ.env ->
  int list Evar.Map.t -> (* ?Y |-> indexes to prune *)
  Evd.evar_map -> (* Σ *)
  ('a, 'b, 'c) Context.Named.Declaration.pt list -> (* ?X's context *)
  Evd.econstr -> (* t *)
  Evd.econstr list -> (* subst for ?X's instanace *)
  Evd.econstr list -> (* spine arguments to ?X[subst] *)
  Evar.t -> (* ?X *)
  (int list Evar.Map.t * Evd.econstr) option

val check_term_restriction : Environ.env -> Evd.evar_map -> EConstr.t list -> bool
