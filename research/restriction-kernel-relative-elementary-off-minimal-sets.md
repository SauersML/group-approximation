---
rg: 2
id: restriction-kernel-relative-elementary-off-minimal-sets
kind: claim
title: If Y ∪ Z contains every minimal subset for some closed invariant Z disjoint from Y, the kernel of EL_n(R_X) → EL_n(R_Y) is E_n(R_X, I_Y)
distinct_from:
  subshift-restriction-kernel-is-relative-elementary: that assumes the limit sets of points outside Y ∪ Z lie in Y ∪ Z; this assumes only that Y ∪ Z contains every minimal subset of X, which covers orbit closures of recurrent points
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `restriction-kernel-off-minimal-sets-proof`.

Setting:
- X ⊆ A^Z is a subshift, Y ⊆ X is closed invariant, and n ≥ 2.
- Some closed invariant Z ⊆ X∖Y satisfies: every minimal subset of X lies in Y ∪ Z.

Conclusions:
- ker(EL_n(R_X) → EL_n(R_Y)) = E_n(I_Y) = E_n(R_X, I_Y).
- For n ≥ 3, K_2(n,R_X) → K_2(n,R_Y) is onto.

Example: X is the orbit closure of a recurrent, not uniformly recurrent point, and Y is its unique minimal subset (`recurrent-orbit-closure-with-unique-sturmian-minimal-set`, with Z = ∅).
