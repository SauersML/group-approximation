---
rg: 2
id: ec-groups-share-the-nonsurjunctive-alphabet-sizes
kind: claim
title: Every existentially closed group fails surjunctivity at exactly the alphabet sizes at which some group fails it
distinct_from:
  surjunctivity-is-axiomatized-by-rectangle-clauses: that proves existentially closed groups decide the conjecture over all alphabets together; this records the transfer size by size and reads off that binary descent for one existentially closed group is the universal descent statement.
  existentially-closed-groups-contain-every-finite-table: that shows an existentially closed group contains every finite table; this applies it to strict data at a fixed alphabet size.
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

**ESTABLISHED** by `ec-groups-share-nonsurjunctive-alphabet-sizes-proof`. Elementary; no novelty is claimed.

For a group `K`, let `NS(K)` be the set of integers `n >= 2` such that some injective, non-surjective
cellular automaton on `A^K` exists with `|A| = n`. Let `NS_all` be the union of `NS(G)` over all groups `G`.

1. If `H <= G`, then `NS(H) ⊆ NS(G)`.
2. If `n ∈ NS(G)` and `l >= 1`, then `nl ∈ NS(G)`.
3. If `K` is existentially closed, then `NS(K) = NS_all`.

**Consequences.**
- `NS_all` is either empty or closed under multiplication by every positive integer. Gottschalk's
  conjecture says it is empty.
- The following are equivalent:
  - (a) `some-nonsurjunctive-group-gives-a-binary-one`;
  - (b) for some existentially closed group `K`, `NS(K) != ∅` implies `2 ∈ NS(K)`;
  - (c) the same for every existentially closed group.

  So `surjunctivity-failure-descends-to-binary-alphabet`, restricted to existentially closed groups, is
  exactly the universal descent statement.
- Once `2 ∈ NS_all`, every even size lies in `NS_all`. Odd sizes are not reached this way.
