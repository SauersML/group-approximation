---
rg: 2
id: leavitt-corner-deviations-are-level-independent
kind: claim
title: The two-root deviation of a Leavitt rank model is the same at every cylinder level
distinct_from:
  corner-rank-data-cannot-contract-the-two-root-deviation: that proves the deviation depends only on the level and that corner data cannot contract it; this is the stronger open assertion that the level-to-level dependence is trivial as well.
  two-root-identity-is-corner-local-for-leavitt-rank-models: that says the deviations at different corners vanish simultaneously; this says they are equal.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, let `sigma` be a characteristic-two rank model of `EL_3(R)`, and let
`delta(k)` be the level-`k` branch deviation, well defined by part 3 of
`corner-rank-data-cannot-contract-the-two-root-deviation`. Then `delta(k) = delta(0)` for every
`k >= 0`.

**Why it matters.** With `leavitt-corner-deviations-vanish-along-levels` it forces `delta(0) = 0`,
hence `N_23 N_12 = 0` on the unit pair, hence `sigma` trivial by corner locality. That is
`rank-models-of-el3-satisfy-the-two-root-identities`, and through
`leavitt-el3-rank-models-over-finite-fields-are-trivial` it makes `R^x` the first group known not to
be linear sofic. Route: `two-root-identity-via-level-contraction`.

## Attempts

* **Level transpositions do not cross levels.** The conjugation that proves level-independence within
  a level uses the cylinder transposition of words of equal length, a unit involution of `R`. No unit
  of `R` carries `e_gamma` to `e_gamma'` for `|gamma| != |gamma'|`, since a unit preserves the
  Murray-von Neumann class and those idempotents are not conjugate by a unit.
* **The corner embedding is not an equality.** Lemma 2.3 of
  `two-root-identity-nonsofic-mechanism-2026-09-12.md` makes `iota_P(x_ab(1))` only simultaneously
  **conjugate** to `x_ab(s_P t_P)`, and Corollary 2.4 records that the shifted pair is not conjugate
  to the unit pair. So the one-level map relates `delta(k+1)` to `delta(k)` by the inequality of
  Proposition 2(5) of `el3-two-root-self-similarity-2026-09-12.md`, not by an equality.
* **Displacements are level-independent, the product is not known to be.** Part 2 of
  `corner-rank-data-cannot-contract-the-two-root-deviation` gives `rho(e_gamma) = rho` at every
  level, because `R ~= R^2`. That is constancy of the single-root data only; the rank of a product of
  two defects is not determined by their individual ranks.
