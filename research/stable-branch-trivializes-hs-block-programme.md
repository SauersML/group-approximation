---
rg: 2
id: stable-branch-trivializes-hs-block-programme
kind: claim
title: On the stable Steinberg branch the Leavitt HS block clauses hold trivially, so those holes restate the branch
distinct_from:
  steinberg-hs-stability-equals-nonhyperlinearity: that closes the fork into an equivalence between HS stability of St_5(L), absence of hyperlinear quotients, and nonhyperlinearity of EL_4(L); this uses that equivalence to show the Leavitt block decomposition and block compatibility claims follow from the stable branch, so they are reformulations of it rather than reductions.
  pointwise-hs-stability-from-no-hyperlinear-quotient: that is the general implication from no hyperlinear quotient to pointwise HS stability; this applies it to the ambient Leavitt group of the compression triple and reads off rank-one block decompositions.
  transported-gap-masa-kills-leavitt-hs-models: that is the forward implication, from the block clauses to triviality of every model; this is the converse, from the stable branch to the block clauses.
---

**ESTABLISHED.**  Let `R = L_(F_2)(1,2)` and let `Gamma = EL_alpha(R) <=
G = EL_D(R)`, `u`, `v` be the configuration of
`openai-nine-leaf-leavitt-configuration`.  Use the house convention that a
`delta`-almost representation `phi : G -> U(d)` has
`||phi(gh) - phi(g) phi(h)||_2 <= delta` on the word ball of radius
`ceil(1/delta)`.

If `leavitt-steinberg-hs-stable` holds, then:

1. `eta(delta) := sup ||phi(s) - 1||_2`, over all `delta`-almost
   representations in all dimensions and all `s in S_G cup {u, v}`, tends
   to `0` as `delta -> 0`.
2. For every `delta`-almost representation, the rank-one projections of
   **any** orthonormal basis satisfy every clause of
   `hs-expander-block-decomposition`.  This uses the corrected mass-weighted
   compressor clause, with `p = 1`, `B_G = B_Gamma`, identity matchings and
   `eps(delta) = 4 eta(delta)^2`; all gap clauses are vacuous on rank-one
   corners.
3. The same rank-one replacement satisfies `leavitt-hs-block-compatibility`
   for every pair of one-level decompositions.

**Consequently these holes restate the branch.**

* `hs-expander-block-decomposition` is equivalent to
  `leavitt-steinberg-hs-stable`.  The forward direction is
  `transported-gap-masa-kills-leavitt-hs-models`.
* Granting the universal `hs-one-level-expander-block-decomposition`,
  `leavitt-hs-block-compatibility` is also equivalent to the branch.
* Neither claim decomposes the stable branch into a smaller problem.  On the
  unstable branch both fail in every faithful model.
* So any argument for them is necessarily an argument excluding faithful
  normalized-HS models of `G`.  A positive synchronization or alignment
  construction cannot succeed in a hyperlinear world: see the model tower in
  `transported-gap-masa-kills-leavitt-hs-models`.

`tracial-median-concentration` holds on the stable branch for the same reason,
and by `transported-gap-masa-kills-leavitt-hs-models` it is not needed by the
Leavitt consumer.

Derivation: `stable-branch-trivializes-hs-block-programme-proof`.
