---
rg: 2
id: odometer-crossed-product-elementary-groups-not-kazhdan
kind: claim
title: Over the dyadic odometer crossed product, a simple LEF ring that is not finitely generated, every EL_n is LEF but not finitely generated, so it has no property (T)
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that is the finitely generated subshift case, where EJZ gives (T); this is the non-expansive odometer, where the ring and every EL_n fail finite generation.
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** by `odometer-crossed-product-elementary-groups-not-kazhdan-proof`.

**Statement.** Let `q` be a prime power, `X = Z_2` the dyadic integers with `Tx = x + 1`, and `R = LC(X, F_q) ⋊_T Z`
(finite sums `Σ f_j u^j`, `u f u^(-1) = f∘T^(-1)`).
1. `R` is simple. It embeds unitally in an algebraic ultraproduct `∏_ω M_(2^K)(F_q)`, so it is a LEF ring. Hence it is stably finite,
   with a faithful Sylvester matrix rank function.
2. `R` is not finitely generated as a ring.
3. For every `n >= 2`, `EL_n(R)` is LEF, hence MF and sofic, and not finitely generated. In particular it has no property (T).

**UN calibration (U2).** Exact tower models and simplicity give LEF groups, not Kazhdan groups. The finitely generated ring that EJZ
needs comes from expansiveness (subshifts), not from towers. The subshift case is `minimal-subshift-algebra-is-simple-lef-ring`. Row 6
of the calibration table.

**Review (un-verify-measure, 2026-09-13): PASS.** Level subrings, exact level-K models and non-finite-generation re-derived. See `research/artifacts/un-review-measure-2026-09-13-part1.md` §C3.
