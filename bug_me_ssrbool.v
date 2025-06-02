Require Import ssrbool.

Require Import ssreflect ssrfun.
Include ssrbool.

Section LocalGlobal.

Variables T1 T2 T3 : predArgType.
Variables (D1 : {pred T1}) (D2 : {pred T2}) (D3 : {pred T3}).
Variables (d1 d1' : mem_pred T1) (d2 d2' : mem_pred T2) (d3 d3' : mem_pred T3).
Variables (f f' : T1 -> T2) (g : T2 -> T1) (h : T3).
Variables (P1 : T1 -> Prop) (P2 : T1 -> T2 -> Prop).
Variable P3 : T1 -> T2 -> T3 -> Prop.
Variable Q1 : (T1 -> T2) -> T1 -> Prop.
Variable Q1l : (T1 -> T2) -> T3 -> T1 -> Prop.
Variable Q2 : (T1 -> T2) -> T1 -> T1 -> Prop.

Hypothesis sub1 : sub_mem d1 d1'.
Hypothesis sub2 : sub_mem d2 d2'.
Hypothesis sub3 : sub_mem d3 d3'.

Require Import Unicoq.Unicoq.
Set Unicoq Debug.
Set Unicoq LaTex File "bug_me.tex".
Set Unicoq Blume FCU.
Lemma can_in_inj' : {in D1, cancel f g} -> {in D1 &, injective f}.
Proof. by move=> fK x y /fK{2}<- /fK{2}<- ->. Qed.

End LocalGlobal.
