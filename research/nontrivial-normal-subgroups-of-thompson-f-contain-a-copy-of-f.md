---
rg: 2
id: nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f
kind: claim
title: Every nontrivial normal subgroup of Thompson's group F contains a subgroup isomorphic to F
distinct_from:
  thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived: that uses the Cannon–Floyd–Parry theorem that nontrivial normal subgroups contain F'; this gives a self-contained proof, from Brin's ubiquity theorem, of the weaker conclusion that such a subgroup contains a copy of F, which is all the closure arguments need.
  hyde-lodha-groups-contain-thompson-commutator-subgroup: that concerns groups of homeomorphisms of the line that contain F'; this is internal to F.
---

**ESTABLISHED.** Let `F ≤ PL_o(I)` be the standard realization: piecewise linear
homeomorphisms of `[0,1]` with finitely many dyadic breakpoints and slopes in `2^Z`.
If `1 ≠ N ◁ F`, then `N` contains a subgroup isomorphic to `F`.

**Consequence used downstream.** If `F_0 ≅ F` is a subgroup of a group `G` and
`N ◁ G`, then either `F_0 ∩ N = 1`, so `F_0` embeds in `G/N`, or `F_0 ∩ N` contains a
copy of `F`.

The proof does not use the Cannon–Floyd–Parry normal subgroup theorem. It takes a
commutator trick to get `N ⊇ [F_J, F_J]` for a small dyadic interval `J`, then applies
Brin's criterion `brin-plo-i-one-sided-approach-gives-a-copy-of-f` to two explicit
commutators.

Proof route: `nontrivial-normal-subgroups-of-f-contain-f-proof`.
