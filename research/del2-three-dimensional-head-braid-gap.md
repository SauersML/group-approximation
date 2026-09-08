---
rg: 2
id: del2-three-dimensional-head-braid-gap
kind: claim
title: Mixtures of the two three-dimensional Jacobson head types have first-braid defect at least one quarter
artifacts:
  - research/artifacts/del2-three-dimensional-head-braid-gap.md
distinct_from:
  jacobson-mixed-packet-attains-rank-eight-below-two: that constructs a dimension-twelve packet with both defects below two; this proves a uniform positive first-braid gap for every packet whose head types are three-dimensional, allowing arbitrary mixing and tail multiplicities.
  jacobson-two-braid-mixed-packet-gap: that asks for a positive gap over all head types and all multiplicities; this establishes a uniform gap only when every head constituent is one of the two three-dimensional irreducibles.
---

Let `G=GL_3(F_2)`, let `K=GL(<e_1,e_3>)` fix `e_2`, and put
`b=w_23`. Let `rho_+,rho_-` be the two conjugate three-dimensional
irreducible unitary representations of `G`. For arbitrary finite unitary
representations `sigma_+,sigma_-` on multiplicity spaces `W_+,W_-`, set

```text
pi(g_Q,g_P)=(rho_+(g_Q) tensor sigma_+(g_P))
             directSum (rho_-(g_Q) tensor sigma_-(g_P)).
```

Either multiplicity space may be zero, but the total space is nonzero.
For every self-adjoint unitary `H` commuting with `pi(K_Q)`,

```text
||(H pi(b,b))^3-I||_op >= 1/4.
```

No condition requires `H` to preserve the two head-isotypic summands.
If only one head type occurs, the stronger bound `1/3` holds.
Thus the first braid alone excludes exact models throughout this family,
including the dimension-twelve packet with tail `1 directSum rho_+`.

Arbitrary trivial-head summands may also be added: their `K`-type is
trivial, so `H` preserves the complementary nonzero three-dimensional
head part, and the same lower bound survives there.

The all-types gap and the non-MF existence endpoint remain open.

DERIVATION
del2-three-dimensional-head-braid-gap-proof
