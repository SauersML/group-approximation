---
rg: 2
id: jacobson-coherent-quotient-has-four-word-gap-criterion
kind: claim
title: The proper coherent quotient retains the head and has an exact four-word matrix-gap criterion
distinct_from:
  jacobson-shift-gap-characterizes-mark-collapse: that concerns the original stable-letter presentation and three errors; this adds the nontrivial coherence relator and completes a third finite group.
  jacobson-laurent-kernel-surjects-natural-affine-module: that disproves coherence in the old presentation; this defines the stronger consistent quotient in which coherence is imposed.
artifacts:
  - research/artifacts/jacobson-coherent-quotient-and-four-word-matrix-gap-2026-09-08.md
---

Let `Gamma=Theta_shift` and use its fully decorated words

```text
b=q_Q q_P,  zeta=r_Q r_P,
u=[h c_P h,k_P],  v=h u h,  D=h zeta h,
W=[u,D] zeta,  E=b v b D.
```

The finitely presented group `Gamma_triangle=Gamma/normalClosure(E)`
is a proper quotient. Its literal action retains the mark `w=x_13,Q`
and the full finitary subgroup `L`. The subgroup `<h,u,b,zeta>`
is a faithful `GL_3(F_2)`, acting diagonally on the disjoint triples
`(e_(1,n+1),e_(2,n),e_(3,n))`, `n>=0`.

On exactly the nonempty admissible domain defining `gamma_shift`, put

```text
gamma_triangle=inf max(
  ||(H rho_B(b))^3-I||, ||W-I||,
  ||T H T^*-H_1||, ||E-I||).
```

The finite packets `B,C` are exact and agree on their full intersection,
the head is nontrivial, and `T` exactly intertwines the specified copies
of `F`. There is no bound on dimension or representation type. Then

```text
0<=gamma_shift<=gamma_triangle<=2,
gamma_triangle>0 iff every norm-corona homomorphism
                     from Gamma_triangle kills w.
```

The zero-infimum direction retains `w` at norm distance two from the
identity. The converse uses finite-group correction and exact finite
intertwining in the original dimensions. Positivity is not proved.

DERIVATION
jacobson-coherent-packet-and-corona-lifting-proof
