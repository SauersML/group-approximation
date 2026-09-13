---
rg: 2
id: no-invariant-measure-steinberg-elementary-no-mf-quotient
kind: claim
title: If the unit space carries no invariant probability measure, elementary groups over the Steinberg algebra have no nontrivial MF quotient from rank 2n
distinct_from:
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that is the ring-level theorem from a properly infinite multiple of the unit; this produces that multiple from the absence of invariant measures on an ample groupoid.
  full-defect-ring-non-mf-at-rank-two: that needs a one-sided inverse in the ring; this needs only a dynamical hypothesis on the groupoid and gives the rank threshold 2n.
  measure-free-ample-groupoid-el-n-full-mf-radical: that is lane un-middle's independent statement of the same groupoid theorem, through (n+1)[R] <= n[R] and a normalized state restricting to an invariant measure; this is the canonical UN node for it, with the explicit type-semigroup route and the threshold 2n, by un-architect's ruling of 2026-09-13.
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

**Canonical UN node** (un-architect ruling, 2026-09-13). Lane `un-middle` independently proved the same theorem as
`measure-free-ample-groupoid-el-n-full-mf-radical`: a normalized state on `V(A_k(𝒢))` restricts to an invariant
measure. Credit both lanes. The UN flagship `free-group-cantor-elementary-group-lef-iff-invariant-measure` cites this
node.

**Review (un-verify, 2026-09-13): PASS.** The monoid map `S(𝒢) → V(A_k(𝒢))`, the ABBL Lemma 2.3 and Rainone–Sims Theorem 6.2 chain (both imports verbatim) and the model tests re-derived. See `research/artifacts/un-review-2026-09-13-part3.md` §§2–3.
