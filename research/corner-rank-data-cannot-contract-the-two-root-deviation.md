---
rg: 2
id: corner-rank-data-cannot-contract-the-two-root-deviation
kind: claim
title: The two-root branch deviation of a Leavitt rank model is constant at positive levels, and corner rank data never contract it
distinct_from:
  el3-two-root-violation-splits-over-leavitt-branches: that gives the exact one-level branch split and an upper bound on the deviation through the branch model; this records constancy of the branch deviation at all positive levels, exact constancy of the root displacements across all corners, and the exact identity at the shifted pair, and it identifies additivity of branch ranks as the only contraction corner data could supply.
  leavitt-rank-models-have-uniform-root-displacement: that bounds and normalizes the displacement of single root elements; this is about the rank of the two-root product and what corner iteration can and cannot do to it.
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is the per-model equivalence between triviality and vanishing of the deviation on any one corner; this quantifies the deviation across corners and rules out contracting it by corner data.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Sections 1-3a; route
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

4. **Constancy at positive levels** (extension by `gk-vf-linear`, Section 56 of its verification
   artifact; re-derived by the author). If `gamma`, `gamma'` are nonempty words of any lengths, then
   `delta_gamma = delta_gamma'`. Choose isometries `Z`, `Z'` with `Z*Z = Z'*Z' = 1`,
   `ZZ* = 1 - e_gamma` and `Z'Z'* = 1 - e_gamma'`. Then `w = s_gamma' t_gamma + Z'Z*` is a unit with
   inverse `s_gamma t_gamma' + ZZ'*` and `w e_gamma w^-1 = e_gamma'`, and `diag(w, w, w)` conjugates.
   So `delta(k) = delta(1)` for every `k >= 1`, and 4 subsumes 3 at positive levels. No unit carries
   `e_gamma` to `e_(empty) = 1`, so this does not reach `delta(0) = rk(N_23 N_12)`.

**Consequence for the gate.** By 4, `delta(1) = rk(n_23(e_0) n_12(e_0))` is the deviation at every
positive level. By Lemma 2.3 of `two-root-identity-nonsofic-mechanism-2026-09-12.md` and
`two-root-identity-is-corner-local-for-leavitt-rank-models`, `delta(1) = 0` exactly when `sigma` is
trivial. The only contraction corner data could supply is additivity of the `2^k` branch ranks at
level `k`, which with 4 would give `delta(1) <= 2^(-k)` for every `k`, hence triviality. Corner data
do not supply it: its natural source, orthogonality of the root branch defects for distinct words,
fails in `rank-modelled-coefficients-violate-two-root-identities`, whose commuting branches act on
tensor factors. That calibration still satisfies the additivity inequality itself, and in a Leavitt
model the inequality would imply triviality, so no calibration over another ring can refute it
(precision remark of `w3-vf-linear`, Section 16.1). So any proof that every characteristic-two rank
model of `EL_3(R)` is trivial must contract the product deviation by a mechanism that is neither
additive over the Cuntz decomposition nor visible in root displacements.

The level form is recorded by `leavitt-corner-deviations-vanish-along-levels`, which by 4 is
equivalent to that triviality statement, and by `leavitt-corner-deviations-are-level-independent`,
which reduces to `delta(1) = delta(0)` and is implied by it. The route
`two-root-identity-via-level-contraction` is a restatement, not a reduction.
