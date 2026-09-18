---
rg: 2
id: crossing-move-hierarchies-have-odd-branching-proof
kind: route
title: End clusters of nested domains are far apart, bounded junctions cannot jump between them, and crossings flip clusters
target: crossing-move-hierarchies-have-odd-branching
requires: []
---

**Setup.** Let `M` be a level-`(k+1)` move with domain `[a, a + d(k+1) - 1]`.
- Its left end cluster is `L = [a, a + c + w]`, and its right end cluster is
  `R = [a + d(k+1) - 1 - c - w, a + d(k+1) - 1]`.
- Each sub-domain has `d(k) >= d(k+1) - c` cells and lies in the parent domain. So each end of a
  sub-domain is within `c` of the corresponding parent end.
- Each sub-move therefore starts and ends in `L` or in `R`: within `w` of a sub-domain end, hence within
  `c + w` of a parent end.

**Two facts.**
- The gap between `L` and `R` is `d(k+1) - 2(c + w) - 2 >= d(k) - 2(c + w) - 2`, which is more than `2B`.
  The head moves at most one cell per step. So the at most `B` steps between consecutive sub-moves never
  carry it from one cluster to the other, and neither do the at most `B` steps before the first
  sub-move or after the last.
- A sub-crossing starts in one cluster and ends in the other, since its sub-domain ends lie in different
  clusters. A sub-return starts and ends in the same cluster.

**Counting.** Track the cluster containing the head through the sequence of sub-moves: it switches
exactly at sub-crossings. `M` starts within `w` of one parent end and ends within `w` of an end, which is
the other end for a crossing and the same end for a return. Hence the number of sub-crossings is odd for
a crossing and even for a return.

**Items 2–3.** If all sub-moves are crossings, their number is odd. If there are exactly two sub-moves,
a crossing needs exactly one sub-crossing and a return needs zero or two. ∎
