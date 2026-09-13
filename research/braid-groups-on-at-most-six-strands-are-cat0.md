---
rg: 2
id: braid-groups-on-at-most-six-strands-are-cat0
kind: claim
title: Braid groups on at most six strands are CAT(0)
distinct_from:
  every-braid-group-is-cat0: that claim is the affirmative answer to Zaremsky Problem 3.6 for all n; this one records the case n <= 6 proved in the literature
---

For every `n <= 6`, the braid group `B_n` acts properly and cocompactly by
isometries on a complete CAT(0) space.

Proof (literature): the dual braid complex of T. Brady is isometric to the
orthoscheme complex `|NCP_n|` of the noncrossing-partition lattice, and
Brady–McCammond reduce CAT(0) of `B_n` to CAT(1) of the diagonal links of
`|NCP_m|`, `m <= n`. Haettel–Kielak–Schwer prove those links are CAT(1) for
`n <= 6` by embedding them into spherical buildings of type A and shrinking
short loops through universal vertices; see
`braid-groups-on-at-most-six-strands-are-cat0-citation`.
