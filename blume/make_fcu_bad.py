#! /usr/bin/python3

f = open('fcu_bad.v', 'w')
def p(s):
    print(s, file=f)
p("Require Import Unicoq.Unicoq.")
p("Set Unicoq Debug.")
p("Set Unicoq Blume FCU.")
p("")


def nat_plus_x(n, var="x"):
    return n*"S(" + var + n*")"

p("Theorem  p : True.")

p("evar (X : nat -> nat).")
a, b = f"(fun x => X ({nat_plus_x(100000)}))", f"(fun x => {nat_plus_x(100005)})"
p(f"munify {a} {b}.")

p("Abort.")


f.close()
