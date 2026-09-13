---
rg: 2
id: el3-leavitt-3-4-has-full-mf-radical
kind: claim
title: Every homomorphism from EL_3(L_K(3,4)) to an MF group is trivial
distinct_from:
  el-n-mf-quotient-below-twice-paradoxical-level-exists: that asks whether SOME ring has an MF quotient in its band; this settles the simplest band instance, L_K(3,4) at N = 3, negatively.
---

For every countable field `K`, every homomorphism from `EL_3(L_K(3,4))` to an MF group is trivial.

- **Place in the band.** `L_K(3,4)` has paradoxical level `p = 3`: `4[R] ≤ 3[R]` holds, while `3[R] ≤ 2[R]` fails in
  `⟨x | 3x = 4x⟩`. So its band is `3 ≤ N < 6`. `non-ibn-ring-el-n-full-mf-radical-above-module-rank` settles
  `N ≥ 4`, so `N = 3` is the only open rank.
- **As a value of the MF spectrum.** In the notation of `mf-rigidity-is-monotone-in-matrix-rank`, rigidity is an
  up-set in `N`. So this claim is exactly `rig(L_K(3,4)) ≤ 3`.
  - Known bound: `rig(L_K(3,4)) ≤ 4`, from `non-ibn-ring-el-n-full-mf-radical-above-module-rank`.
  - The alternative is `rig(L_K(3,4)) = 4`.
  - Matrix amplification cannot decide it. By `mf-thresholds-rescale-under-matrix-amplification`,
    `rig(M_2(L_K(3,4))) = rig(M_3(L_K(3,4))) = 2` whichever value `rig(L_K(3,4)) ∈ {2,3,4}` takes.
  - The general module-type bound is `rig(L_K(m,m+d)) ≤ max(m+1,3)`.
    `leavitt-module-rank-iso-columns-are-not-completable` shows that no completable-column or free-coordinate argument
    can improve it to `rig ≤ m`.
- **Why it matters.** If this claim FAILS, `EL_3(L_K(3,4))` is a finitely generated Kazhdan group
  (`elementary-groups-over-fg-rings-have-property-t`) with a nontrivial MF quotient, inside `EL_4(L_K(3,4))`, which has
  none. That would be the new object of `el-n-mf-quotient-below-twice-paradoxical-level-exists`.

## Attempts
- **Through the conjugate of `EL_4`.** Route `el3-leavitt-3-4-full-mf-radical-via-module-iso-image` reduces this claim
  to `leavitt-3-4-module-iso-image-normally-generates-e3`, which is open.
- **Completable columns and free coordinates: dead.** See `leavitt-module-rank-iso-columns-are-not-completable`.
- **Printed transport inside `EL_3`: silent.** It needs a one-sided inverse with full complement in some `M_j(R)` with
  `2j ≤ 3`, i.e. in `R` itself. But `[R]` is not properly infinite at level 1 (`2x ≤ x` fails in `⟨x | 3x = 4x⟩`).
- **Construction side: no candidate.** `[R]` is paradoxical, so `R` has no state, no Sylvester rank function, and no
  unital map into a matrix ultraproduct. An MF quotient would need operator-norm asymptotic representations that do
  not come from ring approximations.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): Display checked (OPEN node): p(L(3,4)) = 3 and the band reduces to N = 3; the route requires the open normal-generation claim and does not fire.**
