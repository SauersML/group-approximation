---
rg: 2
id: stw99-l-pi1-aut-splits-into-two-hom-groups-proof
kind: route
title: Kill Dadarlat's kernel by lifting unit-evaluation through the UCT
target: stw99-l-pi1-aut-splits-into-two-hom-groups
requires:
  - stw99-l-dadarlat-aut-homotopy-theorem
---

Apply the imported theorem with `X = T`.  What remains is to show that
its kernel vanishes under the present hypotheses -- a point that rank
counting does not supply.

The kernel is `K_0(D)` modulo the image of evaluation at the unit,
`KK(D,D) -> K_0(D)`, `f |-> f(e_D)`.  Write `K_0(D) = Z e_D (+) H`,
which is possible because `e_D` is primitive and `K_0(D)` is finitely
generated free.  Given `a in K_0(D)`, the pair consisting of the
homomorphism `e_D |-> a`, `H |-> 0` on `K_0` and the zero endomorphism of
`K_1` lifts to a class in `KK(D,D)` by the UCT of Rosenberg--Schochet
(https://doi.org/10.1215/S0012-7094-87-05524-4), whose `Ext` terms
vanish here because both K-groups are free.  So evaluation at the unit
is onto and the kernel is zero.

The same UCT computation, in odd degree, identifies `KK^1(D,D)` with
`Hom(K_1(D), K_0(D)) (+) Hom(K_0(D), K_1(D))`, and the surviving
unit-annihilation condition `Delta(e_D) = 0` cuts the second factor down
to `Hom(K_0(D)/Z e_D, K_1(D))`.

Scope: the UCT and Dadarlat's theorem are literature inputs; the kernel
computation above is the argument this route asserts.
