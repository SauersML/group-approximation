---
rg: 2
id: hs-stable-vertex-rounding-for-every-model
kind: claim
title: Every trace-preserving matrix-ultraproduct representation of the actor rounds on the Kazhdan vertex to genuine representations
distinct_from:
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) when the whole actor is coordinatewise genuine; this asks only that the restriction to the Kazhdan vertex round, for every model, with no genuine coordinates assumed.
  el-r-polynomial-robust-spectral-gap: that is the robust spectral gap for asymptotic finite-dimensional representations, free from property (T); this asks for rounding to genuine representations close on generators, which a spectral gap alone does not supply.
  hs-literal-commutant-profile-rounding-is-false: that refutes rounding onto the exact commutant of the supplied matrices; this asks for a nearby genuine representation, a target stable under the perturbation that kills the literal version.
  hs-rounding-and-actor-gap-force-ccr: that is the proved conditional which assumes (H1) for one model and derives normalization; this is (H1) itself, for every model, and nothing proved decides it.
---

**OPEN.** Let `Gamma < G` be an infranormal, non-normal pair of Kazhdan groups, with `(F, kappa)` a Kazhdan
pair for `Gamma`. For every trace-preserving `sigma : G -> U(prod_U M_n)` with coordinates `sigma_n`, after
`o(n)` padding there are genuine representations `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with

```text
max_(s in F) ||sigma_n(s) - pi_n(s)||_2  ->  0   along U.
```

This is hypothesis (H1) of `hs-rounding-and-actor-gap-force-ccr`, required for every model. It is
flexible normalized-HS stability of `Gamma`, restricted to the approximate representations that
extend to trace-preserving representations of `G`.

## Attempts

- **Literal commutant rounding.** Dead (`hs-literal-commutant-profile-rounding-is-false`). A small generic
  perturbation makes the literal commutant scalar, so the rounding target must be a nearby genuine
  representation.
- **Robust spectral gap.** Property (T) gives `(T;FD)^rob` (`el-r-polynomial-robust-spectral-gap`). It moves
  almost invariant vectors of each adjoint representation to invariant ones, but it produces no
  genuine representation close on generators. No mechanism beyond it is recorded.
- **Uniform Kazhdan constants.** Unavailable for the linear Theorem E pair
  (`uniform-kazhdan-fails-for-linear-theorem-e-pair`), so a rounding argument must work at the fixed
  generating set `F`.
- **Genuine coordinate models.** They satisfy it trivially. The content is models with no genuine
  coordinate structure, which is exactly where `kt-centralizer-normalization-hs` is open.
