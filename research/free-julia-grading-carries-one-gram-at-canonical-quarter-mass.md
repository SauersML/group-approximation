---
rg: 2
id: free-julia-grading-carries-one-gram-at-canonical-quarter-mass
kind: claim
title: A free Julia grading carries one Gram operator with canonical quarter mass
distinct_from:
  dihedral-spin-packet-supplies-common-partial-swap: that imposes the central D8 anticommutation relation and therefore makes the off-diagonal block a partial isometry; this uses no relation between the two source involutions, permits an arbitrary contraction Gram block, and obtains its mass from the canonical trace of their commutator word.
  partial-isometry-swap-wordizes-one-bcs-gram-row: that starts from an already supplied partial isometry and constructs its controlled reflection; this starts from one literal reflection and reads its off-diagonal contraction directly.
  controlled-swap-wordizes-matrix-corner-without-adjoint-dilution: that requires a nonlinear controlled copy swap built from a projection; this requires only two freely named involutions and a grading.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial von Neumann algebra and
let `z,j` be self-adjoint unitaries.  Put

```text
P_+=(1+z)/2,              P_-=(1-z)/2,
G=P_+ j P_-.                                             (FJG1)
```

Thus `G` is an arbitrary contraction from the negative grading half to the
positive grading half; no D8 or central-sign relation is imposed.  Define the
ordinary commutator word

```text
w_0=z j z j.                                             (FJG2)
```

Then exactly

```text
||w_0-1||_2^2=8||G||_2^2.                               (FJG3)
```

Now let `d` be another self-adjoint unitary commuting with `z`, and write

```text
A=P_+dP_+,              B=P_-dP_-.
```

For the row word `w_d=d j d j`,

```text
2||AG-GB||_2^2 <= ||w_d-1||_2^2.                       (FJG4)
```

Both constants are independent of the matrix dimension and of the two
grading ranks.

## Canonical-microstate consequence

Suppose a finitely presented group contains involutions represented by
`z,j`, and the group element represented by `w_0` is nontrivial.  In a
canonical normalized-HS microstate, after the fixed involution relations are
spectrally rounded,

```text
tau(w_0)=o(1),                 ||G||_2^2=1/4+o(1).      (FJG5)
```

Thus the single nontrivial word `w_0` authenticates a common Gram operator of
fixed positive mass.  It does not read the matrix dimension and does not use
the trace of a packet projection.

If fixed row involutions `d_r`, all commuting with `z`, decode the two sides
`A_r,B_r` of a finite game and the presentation contains `d_r j d_r j=1`,
then `(FJG4)` makes every one-Gram intertwining residual tend to zero.  Once
the predicate rows have also been decoded, the gap in
`one-gram-vector-decodes-a-finite-bcs-strategy` contradicts `(FJG5)`.

## Exact completeness for an arbitrary Gram contraction

Conversely, let `G:H_- -> H_+` be any nonzero contraction and define its
Julia reflection

```text
j_G = [[(1-GG^*)^(1/2),       G],
       [G^*,             -(1-G^*G)^(1/2)]],
z   = diag(1,-1).                                         (FJG6)
```

Then `j_G=j_G^*=j_G^(-1)`, and `(FJG1)` recovers the original `G`.  If
self-adjoint unitaries `A,B` obey `AG=GB`, then

```text
d=diag(A,B)
```

commutes with `j_G`: the intertwining identity also gives
`A(GG^*)=(GG^*)A` and `B(G^*G)=(G^*G)B`, so functional calculus handles the
two diagonal defect operators in `(FJG6)`.  Hence every zero one-Gram row has
an exact ordinary-word realization, while `G!=0` makes `w_0!=1` by `(FJG3)`.

This removes common-Gram authentication and polar-cut stability from the
one-Gram compiler.  It does **not** manufacture the nonlinear predicate row:
one still has to name a block involution whose positive block is the
predicate reflection and whose negative block is the identity, or provide an
equivalent ordinary-word payment.

