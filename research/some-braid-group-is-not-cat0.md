---
rg: 2
id: some-braid-group-is-not-cat0
kind: claim
title: Some braid group admits no geometric action on a complete CAT(0) space
distinct_from:
  every-braid-group-is-cat0: that claim is the affirmative answer to Zaremsky Problem 3.6; this one is its negation, the negative answer
  some-braid-group-has-no-proper-cat0-action: that claim forbids even proper actions on proper CAT(0) spaces, which is stronger; this one forbids only geometric actions
---

There is `n` such that the braid group `B_n` admits no proper, cocompact,
isometric action on a complete CAT(0) space. This is the negative answer to
Zaremsky Problem 3.6 (`zaremsky-3-06-braid-groups-cat0`).

Any such `n` is at least 8: braid groups with at most 7 strands are CAT(0)
(Haettel–Kielak–Schwer, arXiv:1304.5990, for `n <= 6`; Jeong,
arXiv:2009.09350, for `n = 7`; import nodes pending the full statements).

## Attempts

- **Translation-length (Gersten-type) obstruction.** In a group acting
  properly by semisimple isometries on a CAT(0) space, the translation length
  restricted to a free abelian subgroup is a Euclidean norm (flat torus
  theorem). So if `t` commutes with an infinite-order `a` and `t` is conjugate
  to both `t a^i` and `t a^j` with `0, i, j` distinct, a strictly convex norm
  would take one value at three collinear points: a contradiction. Gersten
  used this to show `Aut(F_3)` is not CAT(0). Where it dies for braids: exponent
  sum and the induced permutation are conjugacy invariants, and for reducible
  braids the fractional Dehn twist coefficients about reducing curves shift
  under twisting, so the needed conjugacies look impossible in `B_n`. Still to
  be written down carefully.
- **Kapovich–Leeb / Bridson mapping class group obstruction.** Their
  arguments against `MCG(S_g)` for `g >= 3` use the genus: centralizers of Dehn
  twists that do not virtually split, or root relations. For `B_n` the
  centralizers of twists split virtually (`P_k = Z x P_k/Z(P_k)`), so the
  obstruction does not transfer as stated.
- Any obstruction must survive the positive cases `n <= 7`, so it has to
  appear only at `n >= 8`: a phenomenon of the noncrossing-partition lattice in
  rank at least 7, or of subgroups that only exist from 8 strands on.
