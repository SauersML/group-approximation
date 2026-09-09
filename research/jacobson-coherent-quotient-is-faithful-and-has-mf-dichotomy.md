---
rg: 2
id: jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy
kind: claim
title: The coherent quotient is the faithful literal group and its head decides MF
distinct_from:
  jacobson-shift-literal-quotient-is-laurent-times-z: that computes the literal symbol quotient but leaves a nontrivial abstract kernel; this proves the single added word normally generates that entire kernel.
  jacobson-coherent-quotient-has-four-word-gap-criterion: that retains the marked finite subgroup without asserting full faithfulness; this identifies the whole new group and its MF radical alternatives.
artifacts:
  - research/artifacts/jacobson-coherent-quotient-is-the-faithful-literal-group-2026-09-08.md
---

For the specific Laurent map and the full bilateral action,

```text
Lambda/normalClosure_Lambda(e) ~= SL_3(F_2[z,z^(-1)]),
normalClosure_Gamma(E)=ker(pi),
Gamma_triangle ~= pi(Gamma).
```

These isomorphisms respect the specified root generators and the marked
head. In `Gamma_triangle`, the finitary normal subgroup `L` has trivial
centralizer. Every homomorphism retaining `w=x_13,Q` is therefore
injective. Consequently

```text
gamma_triangle=0 iff Gamma_triangle is MF,
gamma_triangle>0 iff Gamma_triangle is not MF.
```

The quotient by `L` is the residually finite group
`SL_3(F_2[z,z^(-1)]) x Z`. Thus the MF radical of `Gamma_triangle`
is either `{1}` or `L`; it is `L` exactly when `gamma_triangle>0`.
The dichotomy is established, but which alternative holds remains open.

DERIVATION
jacobson-affine-colimit-and-faithful-head-proof
