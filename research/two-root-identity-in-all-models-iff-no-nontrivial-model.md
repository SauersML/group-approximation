---
rg: 2
id: two-root-identity-in-all-models-iff-no-nontrivial-model
kind: claim
title: The two-root identity holds in every characteristic-two rank model of EL_3(S) exactly when every such model is trivial
distinct_from:
  rank-modelled-coefficients-violate-two-root-identities: that tensor-squares the natural model of a coefficient ring with a unital rank model; this tensor-squares an arbitrary identity-satisfying model, so it applies to rings with no rank model and shows the identity for all models is triviality of all models.
  el3-unit-root-matrix-units-iff-two-root-identities: that characterizes the matrix-unit hypothesis for a single model; this uses it inside the tensor square to show that the identity cannot hold for every model unless every model is trivial.
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

**ESTABLISHED** (proof route `two-root-identity-iff-no-nontrivial-model-proof`; artifact Section 1;
independent re-derivation requested from `w4-vf-gate`).

Let `S` be a unital ring. A *characteristic-two rank model* of `EL_3(S)` is a homomorphism into the
unit group of a rank ultraproduct `prod_U M_(d_n)(F_n)` with every `F_n` of characteristic two, and
`N_ab = sigma(x_ab(1)) - 1`.

1. **Tensor square.** If `sigma` is such a model with `N_23 N_12 = 0`, then `sigma (x) sigma` is
   again such a model, and its root nilpotents satisfy `rk(N'_23 N'_12) = 2 rk(N_12)^2`.
2. **Equivalence.** These are equivalent:
   - (a) every characteristic-two rank model of `EL_3(S)` satisfies `N_23 N_12 = 0`;
   - (b) every characteristic-two rank model of `EL_3(S)` is trivial.

**Consequence.** Over each algebra it covers, `rank-models-of-el3-satisfy-the-two-root-identities` in
characteristic two is the same statement as the absence of nontrivial rank models of `EL_3`. For
`C_2` this turns `cohn-coefficient-el3-rank-models-satisfy-two-root-identity` into the claim that
`EL_3(C_2)` has no nontrivial characteristic-two rank model
(`cohn-elementary-group-rank-radical-is-trivial-or-everything`).
