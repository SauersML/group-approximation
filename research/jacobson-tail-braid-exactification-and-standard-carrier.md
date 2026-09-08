---
rg: 2
id: jacobson-tail-braid-exactification-and-standard-carrier
kind: claim
title: The Jacobson tail braid can be made exact and its standard carrier must cover the head mark
distinct_from:
  jacobson-two-braid-gap-characterizes-mark-collapse: that corrects the finite packet and overlap involution while leaving both braid defects approximate; this corrects the tail braid exactly without changing any finite-packet matrix and gives a quantitative comparison of the two infima.
  jacobson-joint-cells-are-two-braids: that derives equal negative ranks and a four-group multiplicity table below defect two; this parameterizes the exact tail braid by paired positive and negative eigenspaces and bounds the carrier those pairs must supply.
  binary-jacobson-gl3-k-branching-has-regular-counterprofile: that records the head restriction multiplicities without solving the braid equations; this solves the tail braid within each overlap multiplicity space and isolates the remaining first-braid equation.
artifacts:
  - research/artifacts/jacobson-tail-braid-exactification-2026-09-08.md
  - research/artifacts/jacobson-all-head-braid-multiplicity-and-leakage-2026-09-08.md
---

**ESTABLISHED.** Retain the finite packet, involutions, and mark from
`jacobson-two-braid-gap-characterizes-mark-collapse`. Write

```text
B=pi(w_23,w_23),        D=pi(1,w_13),
X=pi(w_23,1),           e=(I-X)/2.
```

For every exact finite-dimensional packet representation `pi` and every
self-adjoint unitary `H` commuting with `pi(K)`, if

```text
epsilon=||(HD)^3-I|| < 2,
```

there is a self-adjoint unitary `H'` commuting with the same `pi(K)` such
that

```text
(H'D)^3=I,
||H'-H|| <= epsilon/2,
||(H'B)^3-I|| <= ||(HB)^3-I|| + 3 epsilon/2.             (1)
```

All packet matrices remain unchanged. Let `gamma_tail` be the infimum of
the first-braid defect over marked exact packets with the tail braid exact.
For the original two-braid infimum `gamma`,

```text
(2/5) gamma_tail <= gamma <= gamma_tail.                 (2)
```

Thus positivity of the original infimum is equivalent to positivity after
imposing the tail braid exactly.

There is an explicit normal form for this remaining problem. Decompose
under `K~=S_3` into irreducible spaces `V_kappa` and multiplicity spaces
`M_kappa`. Since `D` commutes with `K`, write
`M_kappa=M_kappa^+ directSum M_kappa^-` for its two signs. Every exact
tail-braid involution is obtained by choosing equal-dimensional subspaces
`A_kappa^+<=M_kappa^+`, `A_kappa^-<=M_kappa^-` and a unitary
`T_kappa:A_kappa^- -> A_kappa^+`. On their sum its multiplicity matrix is

```text
[ -(1/2)I       (sqrt(3)/2)T_kappa ]
[ (sqrt(3)/2)T_kappa^*       (1/2)I ],                   (3)
```

and it equals `D` on the orthogonal complement. Let `P_std` be the
projection onto the sum of these paired subspaces, with their `K` factors.
Then

```text
P_std=(2I-HD-DH)/3,
(H-D)^2=3P_std.                                         (4)
```

If the tail braid is exact and `delta=||(HB)^3-I||<2`, put `U=HB` and let
`J_std` project onto the sum of the ranges of
`P_std`, `U P_std U^*`, and `U^2 P_std (U^*)^2`. Then

```text
||(I-J_std)e|| <= delta/2,
rank(e) <= rank(J_std) <= 3 rank(P_std).                 (5)
```

In particular, a surviving mark requires a nonzero standard carrier, and
the total paired multiplicity satisfies

```text
sum_kappa dim(V_kappa) dim(A_kappa^+) >= rank(e)/6.       (6)
```

These are reductions and necessary restrictions. They do not prove either
infimum positive: the first braid still couples the selected subspaces and
unitary identifications across the full head packet.

Further multiplicity and leakage restrictions for mixed head packets are
recorded in the [all-head audit](artifacts/jacobson-all-head-braid-multiplicity-and-leakage-2026-09-08.md).

DERIVATION
jacobson-tail-braid-exactification-and-standard-carrier-proof
