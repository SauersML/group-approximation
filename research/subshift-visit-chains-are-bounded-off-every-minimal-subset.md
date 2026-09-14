---
rg: 2
id: subshift-visit-chains-are-bounded-off-every-minimal-subset
kind: claim
title: A closed invariant Y contains every minimal subset of a subshift X iff chains of visits with bounded gaps to clopen sets disjoint from Y are uniformly bounded
distinct_from:
  biasymptotic-subshift-complement-ideal-is-ultramatricial: that derives bounded chains from the limit sets of points outside Y lying in Y; this derives them from Y containing every minimal subset, which also allows recurrent points outside Y
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `subshift-visit-chains-bounded-proof`.

Let X ⊆ A^Z be a subshift and Y ⊆ X closed invariant. The following are equivalent:
- (a) every minimal subset of X lies in Y;
- (b) for every clopen V ⊆ X∖Y and every J ≥ 1 there is M < ∞ with this property: whenever z ∈ X and t_0 < … < t_{m−1} satisfy T^{t_i}z ∈ V and t_{i+1} − t_i ≤ J, we have m ≤ M.

Consequence: for the orbit closure of a recurrent, not uniformly recurrent point whose only minimal subset is Y, visit chains are bounded. This corrects §7 of `research/artifacts/sk-k2-subsystems-2026-09-13-part1.md`.
