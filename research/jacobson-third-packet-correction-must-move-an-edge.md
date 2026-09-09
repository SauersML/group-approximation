---
rg: 2
id: jacobson-third-packet-correction-must-move-an-edge
kind: claim
title: Correcting the third finite packet cannot keep both rank-one restrictions fixed
distinct_from:
  jacobson-first-root-packet-admits-coherent-relative-correction: that corrects one packet relative to a single subgroup and aligns one neighbor; this disproves the analogous statement for two prescribed generating subgroups.
  jacobson-laurent-kernel-surjects-natural-affine-module: that gives a torsion-module quotient and nontriviality of the old word; this gives an integral quotient, infinite order and a continuous finite-dimensional obstruction to a proposed repair.
artifacts:
  - research/artifacts/jacobson-third-packet-cannot-be-corrected-with-both-edges-fixed-2026-09-08.md
---

Let `D=GL_3(F_2)`, with `A=GL_2` on coordinates `1,2` and
`J=GL_2` on coordinates `2,3`. These are exactly the intersections
of the coherent third packet with `C` and `B`, respectively, and
`A intersect J={1}`.

For each `0<theta<pi/2` there is a unital map `f_theta:D->U(8)`
which is an exact representation on both `A` and `J` and satisfies

```text
max_(g,g') ||f_theta(g)f_theta(g')-f_theta(gg')||
  <=6 sin(theta),
```

but no exact representation agrees with both restrictions. If a correction
moves the two restrictions by at most `a,b`, then necessarily
`2 sin(theta)<=3(a+b)`.

The construction also gives exact representations of the original `Gamma`
with all three old mixed errors zero and `||E-I||=2 sin(theta)`.
They kill the head and therefore do not refute the marked matrix gap.
An integral version maps `Lambda` onto `Z^6 semidirect GL_3(F_2)`
and sends `e` to a nonzero lattice vector. In particular the original
words `e` and `E` have infinite order.

DERIVATION
jacobson-integral-twist-and-two-edge-counterexample-proof
