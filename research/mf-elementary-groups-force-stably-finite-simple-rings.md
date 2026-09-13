---
rg: 2
id: mf-elementary-groups-force-stably-finite-simple-rings
kind: claim
title: Over a simple ring, an MF quotient of EL_N forces M_m directly finite for m <= N/2, so stably MF elementary groups force stable finiteness
distinct_from:
  full-defect-in-m-by-m-kills-mf-quotients-of-el-2m: that is the ring-level criterion with an explicit full defect in M_m(R); this is its contrapositive for simple rings, where every infinite amplification has a full defect
  stably-finite-simple-rings-have-mf-elementary-groups: that is the open converse, asking whether stable finiteness suffices; this proves only that it is necessary
  simple-ring-stably-finite-iff-unit-not-paradoxical: that is the ring-level equivalence stably finite <=> no paradox <=> a state on V(R) (un-middle, via KMP's Tarski theorem); this is the group-level consequence, that stably MF elementary groups force those conditions
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that is the paradox-side criterion for any ring, with its simple-ring corollary (un-paradox); this is the contrapositive read on the measure side, with the explicit rank window m <= N/2
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

**ESTABLISHED** (route `mf-elementary-groups-force-stably-finite-simple-rings-proof`; artifact §3). Unreviewed.

Let `R ≠ 0` be a countable simple unital ring.
1. If `M_m(R)` is not directly finite, then for every `N >= 2m`, every homomorphism from `EL_N(R)` to an MF
   group is trivial.
2. If `EL_N(R)` has a nontrivial homomorphism to an MF group (for instance, `EL_N(R)` is MF), then `M_m(R)` is
   directly finite for every `m <= N/2`.
3. If `EL_N(R)` has a nontrivial MF quotient for infinitely many `N` (for instance, `EL_N(R)` is MF for all `N`),
   then `R` is stably finite.

Model tests:
- `L_k(1,2)`: `m = 1`, no MF quotient from rank two. This recovers Cor l.1016 of `non_mf_groups_exist.tex`.
- The Pestov ring `LC(X,F_q) ⋊ Z` is exactly matricial, so the statement is vacuous there, and
  `exactly-matricial-rings-have-lef-general-linear-groups` gives LEF.
- `M_d(F)`: vacuous.

So, for simple rings: exactly matricial ⇒ `EL_N(R)` LEF for all `N` ⇒ MF for all `N` ⇒ stably finite.

**Canonical node for item 1** (un-architect ruling, 2026-09-13). Item 1 is the simple-ring case of the canonical UN
node `stably-infinite-ring-elementary-groups-have-no-mf-quotient` (un-paradox). For simple `R`, `M_m(R)` is not
directly finite iff `(m+1)[R] <= m[R]`: both conditions are upward closed in `m`, with the same least value
(`simple-ring-stably-finite-iff-unit-not-paradoxical`). Items 2 and 3 are this node's own contribution, and the UN
root consumes them for (M⇒). Credit `un-paradox`, `un-middle` and `un-converse`.

**Review (un-verify-3, 2026-09-13): PASS.** Items 1–3 re-derived (`e = 1−st` is a nonzero idempotent and full by simplicity of `M_m(R)`; contrapositive; infinitely many `N` give every `m`). Consistent with `simple-ring-stably-finite-iff-unit-not-paradoxical`. `research/artifacts/un-review3-2026-09-13-part1.md` §5.
