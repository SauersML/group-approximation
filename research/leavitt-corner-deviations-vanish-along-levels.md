---
rg: 2
id: leavitt-corner-deviations-vanish-along-levels
kind: claim
title: The two-root deviation of a Leavitt rank model tends to zero along cylinder levels
distinct_from:
  leavitt-corner-deviations-are-level-independent: that asserts the deviation is constant in the level; this asserts it tends to zero, and the two together force it to be zero.
  corner-rank-data-cannot-contract-the-two-root-deviation: that proves corner data alone supplies no contraction, since branch-rank additivity is refuted; this is the contraction itself, which must therefore come from elsewhere.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, let `sigma` be a characteristic-two rank model of `EL_3(R)`, and let
`delta(k)` be the level-`k` branch deviation of part 3 of
`corner-rank-data-cannot-contract-the-two-root-deviation`. Then `delta(k) -> 0` as `k -> infinity`.

**Why it matters.** With `leavitt-corner-deviations-are-level-independent` it gives the gate; see
`two-root-identity-via-level-contraction`.

## Attempts

* **Additivity of branch ranks would give it, and corner data do not supply it.** The Cuntz
  relation puts `2^k` branch products at level `k`, all of rank `delta(k)`. If
  `sum_{|gamma| = k} rk(P_gamma) <= 1`, then `delta(k) <= 2^(-k)`. The natural source of that
  inequality, orthogonality of the root branch defects `a_gamma`, `b_gamma`, fails in the natural
  tensor square of `rank-modelled-coefficients-violate-two-root-identities` (deviation `2/9` over
  `D = colim M_(2^k)(F_2)`). But that calibration still satisfies the inequality
  (`sum_gamma rk(P_gamma) = 2^(1-k)/9`), and in a Leavitt model the inequality implies this claim,
  so no calibration over another ring can refute it. Correction after `w3-vf-linear`, Section 16.1;
  an earlier version said additivity is refuted.
* **Proposition 2(5) is an upper bound with the wrong constant.** It gives
  `delta(k) <= 2 delta(k+1) + rk(C_k)`, which bounds the coarser level by the finer one and so does
  not iterate downwards.
* **Support halving is unavailable.** If the globality of
  `leavitt-rank-models-kazhdan-fixed-ideals-are-global` applies to `iota_0(R^x)`, the branch model has
  the same fixed right ideal as `sigma`, so branches cannot live on half the space. That is recorded
  in Section 6 of `el3-two-root-self-similarity-2026-09-12.md` and was not re-derived there.
* **Displacement data cannot see it.** By part 2 of
  `corner-rank-data-cannot-contract-the-two-root-deviation` the root displacements are exactly
  constant across levels, so any contraction is invisible to them and must act on the product.
