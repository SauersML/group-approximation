---
rg: 2
id: no-invariant-measure-steinberg-elementary-no-mf-quotient
kind: claim
title: If the unit space carries no invariant probability measure, elementary groups over the Steinberg algebra have no nontrivial MF quotient from rank 2n
distinct_from:
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that is the ring-level theorem from a properly infinite multiple of the unit; this produces that multiple from the absence of invariant measures on an ample groupoid.
  full-defect-ring-non-mf-at-rank-two: that needs a one-sided inverse in the ring; this needs only a dynamical hypothesis on the groupoid and gives the rank threshold 2n.
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

Let `𝒢` be an ample, Hausdorff, second countable groupoid with compact unit space `X`, and let `k` be
a countable field. Suppose `X` carries no `𝒢`-invariant Borel probability measure. Then:

1. `2n[1] <= n[1]` in `V(A_k(𝒢))` for some `n >= 1`.
2. For every `N >= 2n`, every homomorphism from `EL_N(A_k(𝒢))` to an MF group is trivial.

If `2[X] <= [X]` in the type semigroup `S(𝒢)`, one may take `n = 1`, so the conclusion holds from
rank 2.

- No minimality, effectiveness or simplicity is assumed.
- **Model tests.**
  - For the Cuntz groupoid, `S(𝒢)` has `[X] = 2[X]`, and the conclusion recovers the printed Leavitt
    case.
  - For a minimal subshift over `Z` there is an invariant measure, so the claim says nothing there.
    Consistently, `EL_3` of the Pestov 9.1 ring is LEF.

Unreviewed proof in the artifact (Sections 1–3). It uses a monoid homomorphism
`S(𝒢) -> V(A_k(𝒢))`, `[U] ↦ [1_U]`, from `1_V * 1_(V^(-1)) = 1_(r(V))`.
