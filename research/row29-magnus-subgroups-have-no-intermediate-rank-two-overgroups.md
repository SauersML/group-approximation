---
rg: 2
id: row29-magnus-subgroups-have-no-intermediate-rank-two-overgroups
kind: claim
title: The Magnus subgroups of the last length-15 residue class have no rank-two overgroups strictly inside the free Magnus piece
distinct_from:
  amenable-envelope-magnus-piece-one-relator-sofic: that is the positive criterion (an amenable envelope of the Magnus piece over a Magnus subgroup gives soficity); this is a subgroup-lattice fact about one specific Magnus piece, which closes one recorded shape an envelope could take and proves nothing about soficity.
  unpeelable-extreme-one-relator-groups-sofic: that is the open soficity claim; this is a finite, elementary statement about the rank-two subgroups of F(x,y) containing the Magnus subgroups of its last uncertified length-15 class.
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
  - research/artifacts/one-relator-magnus-row29-scripts/algext.py
  - research/artifacts/one-relator-magnus-row29-scripts/algext.out
---

**Setting.** Row 29 of the length-15 residue is `G = <a,t | AAttATaTAttaaTT>`.
With `a_h = t^h a t^(-h)` its Magnus rewriting is
`W_0 = a_0^(-2) a_2^(-1) a_1 a_0^(-1) a_2^2`, level exponent sums `[-3, 1, 1]`
(`research/artifacts/or-length15-residue-scripts/residue-output.txt`, line 36).
So the Magnus piece is `B_0 = F(x,y)` with `x = a_0`, `y = a_2`, and
`a_1 = v^(-1)` for

    v = x^(-1) y^2 x^(-2) y^(-1).

The Magnus subgroups are `F_- = <a_0, a_1> = <x, v>` and `F_+ = <a_1, a_2> = <v, y>`.

**Claim.** `F_-` and `F_+` are free of rank 2 and of infinite index in `F = F(x,y)`,
and they have no proper rank-two overgroups other than `F`. If `K <= F` has rank at
most 2 and `F_- <= K`, then `K = F_-` or `K = F`. The same holds for `F_+`.

**Consequence.** Every infinite cyclic splitting of `F` (an amalgam over `Z`, or an
HNN extension over `Z`) has vertex groups of rank at most 2. This follows from the
Euler characteristic of a graph of free groups with cyclic edge groups:
`-1 = (1 - r_A) + (1 - r_B)` for `A *_Z B`, and `-1 = 1 - r_A` for `A *_Z`. A
vertex group is a proper subgroup of `F`. So a vertex group containing `F_-` or `F_+`
equals it. The shape recorded in Attempt 5 of
`unpeelable-extreme-one-relator-groups-sofic` ("an infinite cyclic splitting of
`F(x,y)` whose rank-2 vertex group properly contains a Magnus subgroup") therefore
never occurs for row 29. What is left of the amenable-envelope route for this class
is `F_-` or `F_+` being itself a vertex group of a cyclic splitting of `F`. This
claim does not decide that case.

No novelty is claimed; the argument is elementary Stallings folding plus a finite
enumeration (15 vertex partitions for `F_-`, 52 for `F_+`).
