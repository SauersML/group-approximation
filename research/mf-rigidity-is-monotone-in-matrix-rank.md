---
rg: 2
id: mf-rigidity-is-monotone-in-matrix-rank
kind: claim
title: Being MF is a down-set and having a full MF radical is an up-set in the matrix rank, so every ring has two MF thresholds
distinct_from:
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that gives a sufficient ring hypothesis for rigidity above a computed rank; this says nothing about which rings are rigid and only that the set of rigid ranks is upward closed.
  full-defect-ring-non-mf-at-rank-two: that is the manuscript's rank-two theorem under a full complementary idempotent; this is the rank-structural statement that holds for every ring with no hypothesis.
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

Let `R` be a countable unital ring with `1 != 0`. Call `EL_N(R)` **MF-rigid** if every homomorphism from
`EL_N(R)` to an MF group is trivial, that is `Rad_MF(EL_N(R)) = EL_N(R)`.

**Theorem.** For `2 <= N <= M`:

- if `EL_M(R)` is MF then `EL_N(R)` is MF;
- if `EL_N(R)` is MF-rigid then `EL_M(R)` is MF-rigid;
- `EL_N(R)` is never both MF and MF-rigid.

**Corollary (the MF spectrum).** With

```text
mf(R)  = sup{ N >= 2 : EL_N(R) is MF }          (sup of the empty set = 1)
rig(R) = min{ N >= 2 : EL_N(R) is MF-rigid }    (min of the empty set = infinity)
```

one has `mf(R) < rig(R)`, and the ranks `N >= 2` fall into three consecutive regimes: `EL_N(R)` is MF for
`N <= mf(R)`; is not MF but has a nontrivial MF quotient for `mf(R) < N < rig(R)`; and is MF-rigid for
`N >= rig(R)`.

Consequences for the UN program:

- Every rank-quantified theorem is an upper bound on one integer. The manuscript's rank-two theorem says
  `rig(R) = 2` under `ts = 1` and `R(1-st)R = R`; `stably-infinite-ring-elementary-groups-have-no-mf-quotient`
  says `2n[1] <= n[1]` gives `rig(R) <= 2n`; `non-ibn-ring-el-n-full-mf-radical-above-module-rank` says
  `R^m ~= R^(m+d)` gives `rig(R) <= max(m+1, 3)`.
- The open low-rank band `3 <= N < 2p` of lane `un-middle` is exactly the computation of `rig(R)` below the
  known bound, so it asks for a value and not for a dichotomy.
- The two calibrating rings sit at the two extremes: `(mf, rig) = (infinity, infinity)` for the Pestov ring
  `LC(X,F_q) ⋊ Z`, which is LEF, and `(1, 2)` for `L_k(1,2)`.
- Rung (M) of the root `kazhdan-elementary-approximation-type-mirrors-ring-type` becomes coherent: "MF-rigid
  for some rank" and "MF-rigid for all large ranks" are the same condition.

The proof is elementary and uses only that MF passes to subgroups, together with the fact that for `N >= 2`
the normal closure of `EL_N(R)` inside `EL_M(R)` is all of `EL_M(R)`. It is written out in the route and in
the artifact, Section 2.
