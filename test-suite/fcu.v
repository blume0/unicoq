

Require Import Unicoq.Unicoq.
Set Unicoq Debug.
Set Unicoq LaTex File "fcu.tex".



(* An example where the FCU-extended Meta-Inst succeeds and the
   HOPU Meta-Inst fails *)
Set Unicoq Blume FCU.
Theorem tt : True.
  evar (Y : Type).
  evar (X : Y).
  Unset Unicoq Blume FCU.
  Fail munify (fun x => X (S x)) (fun x => (S x, O)).
  Set Unicoq Blume FCU.
  munify (fun x => X (S x)) (fun x => (S x, O)).
Abort.



(* Same example but formulated in a more "natural" way *)
Import EqNotations.

(* I expected it to work with the following, but it does not:
   it is elaborated into two equations:
   ?X[] ?x[...] ?=? (S (S x) = 0)                   (1)
   (?x[x:=x;a:=a;b:=b] = ?y[...]) ?=? (S x = 0)     (2)
   If (2) was solved first, we would get ?x := S x and the (1)
   equation would become ?X (S x) ?=? (S (S x) = 0) which falls under FCU
   But the algorithm solves (1) first using the First-Order
   heuristic, which leads to the bad "?X:= eq_refl (S (S x))" solution *)
Fail Check let X := _ in fun x (a : S x = 0) (b : S (S x) = 0) => rew [X] a in b.
(* By specifying explicitly the solution for ?x in the above system, we get the
   following working example *)
Check let X := _ in fun x (a : S x = 0) (b : (S (S x) = 0)) => eq_rect (S x) X b _ a.
Unset Unicoq Blume FCU.
Fail Check let X := _ in fun x (a : S x = 0) (b : (S (S x) = 0)) => eq_rect (S x) X b _ a.

Print Unicoq Stats.
