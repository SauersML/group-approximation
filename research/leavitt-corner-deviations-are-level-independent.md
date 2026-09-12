---
rg: 2
id: leavitt-corner-deviations-are-level-independent
kind: claim
title: The two-root deviation of a Leavitt rank model is the same at every cylinder level
distinct_from:
  corner-rank-data-cannot-contract-the-two-root-deviation: that proves the branch deviation is constant at all positive levels and that corner data cannot contract it; this is the open assertion that the positive-level value equals the unit-pair value.
  two-root-identity-is-corner-local-for-leavitt-rank-models: that says the deviations at different corners vanish simultaneously; this says they are equal.
artifacts:
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, let `sigma` be a characteristic-two rank model of `EL_3(R)`, and let
`delta(k)` be the level-`k` branch deviation, well defined by part 3 of
`corner-rank-data-cannot-contract-the-two-root-deviation`. Then `delta(k) = delta(0)` for every
`k >= 0`.

**Reduction.** Part 4 of `corner-rank-data-cannot-contract-the-two-root-deviation` gives
`delta(k) = delta(1)` for every `k >= 1`. So this claim is exactly

```text
rk( N_23 N_12 ) = delta(0) = delta(1) = rk( n_23(e_0) n_12(e_0) ) .
```

It follows from `leavitt-corner-deviations-vanish-along-levels`, which with corner locality makes both
sides zero.

**What it records.** It compares the unit-pair deviation with the first-level corner deviation. Both
vanish exactly when `sigma` is trivial, by `two-root-identity-is-corner-local-for-leavitt-rank-models`
and Lemma 2.3 of `two-root-identity-nonsofic-mechanism-2026-09-12.md`, but no equality between them
is known. It is weaker than the binary gate. No route requires it: the earlier version of
`two-root-identity-via-level-contraction` did, and there it was redundant (`gk-vf-linear`,
Section 56).

## Attempts

* **Positive levels are conjugate; only the unit level is not.** For nonempty `gamma`, `gamma'` of any
  lengths, the unit `w = s_gamma' t_gamma + Z'Z*` of part 4 of
  `corner-rank-data-cannot-contract-the-two-root-deviation` carries `e_gamma` to `e_gamma'`. No unit
  carries `e_gamma` to `e_(empty) = 1`, so conjugation cannot compare `delta(1)` with `delta(0)`.
  (Corrected after `gk-vf-linear`, Section 56. An earlier version said no unit of `R` carries
  `e_gamma` to `e_gamma'` when `|gamma| != |gamma'|`. That is false for nonempty words.)
* **The corner embedding is not an equality.** Lemma 2.3 of
  `two-root-identity-nonsofic-mechanism-2026-09-12.md` makes `iota_P(x_ab(1))` only simultaneously
  **conjugate** to `x_ab(s_P t_P)`, and Corollary 2.4 records that the shifted pair is not conjugate
  to the unit pair. So Proposition 2(5) of `el3-two-root-self-similarity-2026-09-12.md` gives only
  `delta(0) <= 2 delta(1) + rk(C)`, not an equality.
* **Displacements are constant at every level; the product is constant only at positive levels.**
  Part 2 of `corner-rank-data-cannot-contract-the-two-root-deviation` gives `rho(e_gamma) = rho` at
  every level, including the empty word. Part 4 gives constancy of the product rank for nonempty
  words only. The rank of a product of two defects is not determined by their individual ranks.

*Correction by `gk-vf-linear` (2026-09-12), Section 56 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: the first Attempts bullet is false for nonempty words. `w = s_gamma' t_gamma + Z' Z*` is a unit with `w e_gamma w^-1 = e_gamma'` for any nonempty `gamma`, `gamma'`, so `delta(k) = delta(1)` for `k >= 1`. This claim reduces to `delta(1) = delta(0)`, and it follows from `leavitt-corner-deviations-vanish-along-levels`.*
