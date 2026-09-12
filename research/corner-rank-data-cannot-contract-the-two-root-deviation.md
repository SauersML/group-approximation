---
rg: 2
id: corner-rank-data-cannot-contract-the-two-root-deviation
kind: claim
title: Corner and branch rank data of a Leavitt rank model determine the two-root deviation by level alone and never contract it
distinct_from:
  el3-two-root-violation-splits-over-leavitt-branches: that gives the exact one-level branch split and an upper bound on the deviation through the branch model; this records level-independence of the branch deviation at every level, exact constancy of the root displacements across all corners, and the exact identity at the shifted pair, and it identifies additivity of branch ranks as the only contraction corner data could supply.
  leavitt-rank-models-have-uniform-root-displacement: that bounds and normalizes the displacement of single root elements; this is about the rank of the two-root product and what corner iteration can and cannot do to it.
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is the per-model equivalence between triviality and vanishing of the deviation on any one corner; this quantifies the deviation across corners and rules out contracting it by corner data.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Sections 1-3; route
`corner-rank-no-contraction-proof`). Let `R = L_(F_2)(1,2)`, let `M` be a rank ultraproduct over a
field of characteristic two and let `sigma : EL_3(R) -> M^x` be a homomorphism. Write
`n_ab(r) = sigma(x_ab(r)) - 1`, `rho(a) = rk(n_12(a))`, `rho = rho(1)`, and for a finite word `gamma`
over `{0,1}` put `e_gamma = s_gamma t_gamma`,

```text
P_gamma = n_23(e_gamma) n_12(e_gamma),   delta_gamma = rk(P_gamma),
delta_sh = rk( n_23(s_0) n_12(t_0) ) .
```

1. **Deviation identity at the shifted pair.** With `X = n_12(t_0)` and `Y = n_23(s_0)`,

   ```text
   rk( n_13(1) - X Y ) = rk( Y X ) = delta_sh ,
   ```

   and therefore `| rk(X Y) - rho | <= delta_sh` and `rho <= delta_sh + rk(X Y)`. So the
   non-vanishing order of the product is pinned to `rho` within `delta_sh`.

2. **Displacement constancy across corners.** `rho(e_gamma) = rho` and `rk(n_13(e_gamma)) = rho` for
   every word `gamma`. So corner iteration does not contract the displacement of any single root
   element: a halving identity for `rho` is false, not merely unavailable. The reason is `R ~= R^2`,
   which makes every nonzero corner of `R` isomorphic to `R`.

3. **Level-independence of the branch deviation.** If `|gamma| = |gamma'|` then
   `delta_gamma = delta_gamma'`, by conjugating with `diag(w, w, w)` for the level-`k` cylinder
   transposition `w`, which is a unit involution of `R`. So `delta(k) := delta_gamma` for
   `|gamma| = k` is well defined.

**Consequence for the gate.** The only contraction corner data could supply is additivity of the
`2^k` branch ranks at level `k`, which with 3 would give `delta(k) <= 2^(-k)`. Additivity is refuted
by `rank-modelled-coefficients-violate-two-root-identities`, whose commuting branches act on tensor
factors. So any proof of `rank-models-of-el3-satisfy-the-two-root-identities` must contract the
product deviation by a mechanism that is neither additive over the Cuntz decomposition nor visible
in root displacements. The surviving form is the pair of open claims
`leavitt-corner-deviations-are-level-independent` and
`leavitt-corner-deviations-vanish-along-levels`, wired by
`two-root-identity-via-level-contraction`.
