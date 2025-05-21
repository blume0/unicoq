

Require Import Unicoq.Unicoq.
Set Unicoq Debug.
Set Unicoq LaTex File "fcu.tex".



Set Unicoq Blume FCU.
Theorem tt : True.
  evar (Y : Type).
  evar (X : Y).
  Unset Unicoq Blume FCU.
  Fail munify (fun x => X (S x)) (fun x => (S x, O)).
  Set Unicoq Blume FCU.
  munify (fun x => X (S x)) (fun x => (S x, O)).
Abort.


Import EqNotations.
Check let X := _ in fun x (a : S x = 0) (b : (S (S x) = 0)) => eq_rect (S x) X b _ a.
Unset Unicoq Blume FCU.
Fail Check let X := _ in fun x (a : S x = 0) (b : (S (S x) = 0)) => eq_rect (S x) X b _ a.

Print Unicoq Stats.
