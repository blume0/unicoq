

Require Import Unicoq.Unicoq.
Set Unicoq Debug.
Set Unicoq LaTex File "fcu.tex".



Set Unicoq Blume FCU.
Theorem hehe : True.
  evar (Y : Type).
  evar (X : Y).
  Unset Unicoq Blume FCU.
  Fail munify (fun x => X (S x)) (fun x => (S x, O)).
  Set Unicoq Blume FCU.
  munify (fun x => X (S x)) (fun x => (S x, O)).
Abort.


Print Unicoq Stats.
