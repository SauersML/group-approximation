---
rg: 2
id: every-closed-surface-mcg-embeds-in-some-out-free-group
kind: claim
title: For every g some Out(F_n) contains a subgroup isomorphic to the mapping class group of the closed genus-g surface
distinct_from:
  every-closed-surface-mcg-embeds-in-some-aut-free-group: that asks for a host Aut(F_n); this asks for a host Out(F_n), which a yes there implies through Aut(F_n) inside Out(F_(n+1)), while the converse implication is not known.
---

**OPEN.** For every `g ≥ 0`, the orientation-preserving mapping class group
`MCG(S_g)` of the closed orientable surface of genus `g` embeds in some
`Out(F_n)`.

- `g ≤ 2`: established, through `low-genus-closed-mcgs-embed-in-aut-free-groups`
  and item 3 of `aut-free-embeddability-passes-to-finite-index-overgroups`. No
  route records it separately, since the full claim quantifies over all `g`.
- Implied by `every-closed-surface-mcg-embeds-in-some-aut-free-group`
  (route `closed-mcg-out-embedding-via-aut-embedding`).
- Any host has `n ≥ 2g − 1` for `g ≥ 2`
  (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).

This is the affirmative answer to the Out-host question of Zaremsky Problem 3.10
(`zaremsky-3-10b-by-yes`).

## Attempts

1. **Through an Aut host.** Route `closed-mcg-out-embedding-via-aut-embedding`.
2. **Out-embeddability is not known to pass to finite-index overgroups.** Inducing
   an outer action to a free product of copies gives automorphisms only modulo
   automorphisms that are inner on each factor separately, and those need not be
   inner in the free product (scope note of
   `aut-free-embeddability-passes-to-finite-index-overgroups`). So, unlike for Aut
   hosts, torsion in `MCG(S_g)` is still a possible place for an obstruction here.
3. **Dehn--Nielsen--Baer.** `MCG(S_g)` sits in `Out(π_1 S_g)`, but `π_1 S_g` is
   not free, and a closed surface group has no characteristic finitely generated
   normal subgroup of infinite index to replace it.
