---
rg: 2
id: every-out-free-group-embeds-in-some-aut-free-group
kind: claim
title: For every m some Aut(F_n) contains a subgroup isomorphic to Out(F_m)
distinct_from:
  out-free-groups-virtually-embed-in-aut-free-groups: that asks, for each rank at least three, for a finite-index subgroup of Out(F_n) inside some Aut(F_m); this asks for all of Out(F_m) in every rank, and the two are equivalent rank by rank for m at least three by aut-free-embeddability-passes-to-finite-index-overgroups.
  low-rank-out-free-groups-embed-in-aut-free-groups: that is the established case of rank at most two; this is the statement in every rank.
---

**OPEN.** For every `m ≥ 0` there are `n` and an injective homomorphism
`Out(F_m) → Aut(F_n)`.

- `m ≤ 2`: established, `low-rank-out-free-groups-embed-in-aut-free-groups`.
- `m ≥ 3`: equivalent to `out-free-groups-virtually-embed-in-aut-free-groups`
  at rank `m`. The routes `out-fm-aut-embedding-via-virtual-embedding` and
  `out-fn-virtual-embedding-from-full-embedding` record both directions.
- Any host has `n ≥ m` (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).

This is the affirmative answer to the first question of Zaremsky Problem 3.10
(`zaremsky-3-10a-by-yes`).

## Attempts

1. **Virtual sections of `Aut(F_m) → Out(F_m)`.** A section over a finite-index
   subgroup gives the claim at rank `m` with `n = m·[Out(F_m) : L]`. Undecided for
   `m ≥ 3`. Rational cohomology with coefficients pulled back from `Out(F_m)`
   cannot obstruct one (`aut-out-free-abelianized-extension-splits-rationally`);
   a section restricted to one factor of a rank-one splitting is standard or fixes
   one big vertex (`free-splitting-fa-lifts-choose-a-side`).
2. **Larger rank preserving a free splitting.** Reduces to item 1 for `m ≥ 4`
   (`free-splitting-compatible-aut-lifts-are-virtual-sections`).
3. **Restriction to a characteristic finite-index subgroup.** Lands in `Out`,
   not `Aut` (Attempts of `out-free-groups-virtually-embed-in-aut-free-groups`).
4. **What remains untried.** By `aut-free-embeddability-passes-to-finite-index-overgroups`
   any faithful action of any finite-index subgroup on any finitely generated free
   group suffices. Such an action need not be related to the outer action on
   `F_m`, and need not preserve a free factor, so items 1 and 2 do not cover it.
   No candidate of that kind is known.
