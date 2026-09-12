---
rg: 2
id: leavitt-corner-deviations-vanish-along-levels
kind: claim
title: The two-root deviation of a Leavitt rank model tends to zero along cylinder levels
distinct_from:
  leavitt-corner-deviations-are-level-independent: that asserts the unit-pair deviation equals the first-level corner deviation; this asserts the positive-level deviation is zero, which implies that one.
  corner-rank-data-cannot-contract-the-two-root-deviation: that proves the branch deviation is constant at positive levels and that corner data do not supply a contraction; this is the vanishing itself, which must therefore come from elsewhere.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, let `sigma` be a characteristic-two rank model of `EL_3(R)`, and let
`delta(k)` be the level-`k` branch deviation of parts 3-4 of
`corner-rank-data-cannot-contract-the-two-root-deviation`. Then `delta(k) -> 0` as `k -> infinity`.

**Equivalent form: this is the binary gate.** Part 4 of
`corner-rank-data-cannot-contract-the-two-root-deviation` gives `delta(k) = delta(1)` for every
`k >= 1`. So this claim says `delta(1) = rk(n_23(e_0) n_12(e_0)) = 0` for every `sigma`. By Lemma 2.3
of `two-root-identity-nonsofic-mechanism-2026-09-12.md` and
`two-root-identity-is-corner-local-for-leavitt-rank-models`, that holds for `sigma` exactly when
`sigma` is trivial. Quantified over all `sigma`, this claim is therefore exactly: every
characteristic-two rank model of `EL_3(L_(F_2)(1,2))` is trivial. It is the binary gate in
branch-deviation form, not half of it (`gk-vf-linear`, Section 56).

**Why it matters.** It feeds `non-linear-sofic-group` through the restatement route
`two-root-identity-via-level-contraction`.

## Attempts

* **Additivity of branch ranks would give it, and corner data do not supply it.** The Cuntz
  relation puts `2^k` branch products at level `k`, all of rank `delta(k) = delta(1)`. If
  `sum_{|gamma| = k} rk(P_gamma) <= 1`, then `delta(1) <= 2^(-k)` for every `k`, so `delta(1) = 0`.
  The natural source of that inequality, orthogonality of the root branch defects `a_gamma`,
  `b_gamma`, fails in the natural tensor square of
  `rank-modelled-coefficients-violate-two-root-identities` (deviation `2/9` over
  `D = colim M_(2^k)(F_2)`). But that calibration still satisfies the inequality
  (`sum_gamma rk(P_gamma) = 2^(1-k)/9`), and in a Leavitt model the inequality implies this claim,
  so no calibration over another ring can refute it. Correction after `w3-vf-linear`, Section 16.1;
  an earlier version said additivity is refuted. Over `D` the deviation `2 . 4^(-k) / 9` is not
  constant in `k`, because `D` has no unit carrying `e_gamma` across levels.
* **Proposition 2(5) bounds the wrong level.** It gives `delta(0) <= 2 delta(1) + rk(C)`, which bounds
  the unit level by the first. With constancy at positive levels it says nothing about `delta(1)`
  itself.
* **Support halving is unavailable.** If the globality of
  `leavitt-rank-models-kazhdan-fixed-ideals-are-global` applies to `iota_0(R^x)`, the branch model has
  the same fixed right ideal as `sigma`, so branches cannot live on half the space. That is recorded
  in Section 6 of `el3-two-root-self-similarity-2026-09-12.md` and was not re-derived there.
* **Displacement data cannot see it.** By part 2 of
  `corner-rank-data-cannot-contract-the-two-root-deviation` the root displacements are exactly
  constant across levels, so any contraction is invisible to them and must act on the product.

*Note by `gk-vf-linear` (2026-09-12), Section 56 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: since `delta(k) = delta(1)` for `k >= 1`, this claim is equivalent to `delta(1) = 0` for every model. By corner locality, that means every characteristic-two rank model of `EL_3(L_(F_2)(1,2))` is trivial: it is the binary gate itself.*
