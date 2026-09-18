---
rg: 2
id: one-mod-k-partition-posets-are-highly-connected
kind: claim
title: The proper part of the 1 mod k partition lattice on tk+1 points is a wedge of (t-2)-spheres, hence (t-3)-connected
distinct_from:
  germ-complex-and-bux-gonzalez-morse-inputs: that imports the germ complex and a Morse Lemma; this imports the homotopy type of a finite combinatorial poset, the 1 mod k partition lattice, which serves as a descending link.
---

**ESTABLISHED by citation plus a short check (route `one-mod-k-partition-posets-are-highly-connected-proof`;
unreviewed).**

Fix integers `k >= 1` and `t >= 1`, and put `n = tk + 1`. Let `Π^{1 mod k}_n` be the set of partitions of
`[n] = {1, ..., n}` whose block sizes are all `≡ 1 mod k`, ordered by refinement. Its bottom is the discrete
partition and its top is the one-block partition. Its **proper part** `Π̄^{1 mod k}_n` is what remains after both are
removed. Then:

1. `Π^{1 mod k}_n` is graded of length `t`: a partition with `b` blocks has rank `(n − b)/k`.
2. It is totally semimodular.
3. The order complex of `Π̄^{1 mod k}_n` has the homotopy type of a wedge of spheres of dimension `t − 2`, possibly an
   empty wedge. In particular it is `(t − 3)`-connected.
4. **Rank selection.** For `1 <= s <= t − 1`, the subposet of partitions of rank `1, ..., s` has the homotopy type of a
   wedge of `(s − 1)`-spheres, so it is `(s − 2)`-connected. These are the partitions with
   `n − sk <= b <= n − k` blocks.

For `k = 1` this is the partition lattice `Π_n`, whose proper part is a wedge of `(n − 1)!` spheres of dimension
`n − 3` (Björner). For `k = 2` it is the odd block size partition lattice.

**Use.** Let `P` be a partition of a set into `n` pieces. Consider the coarsenings of `P`, other than `P` itself,
whose blocks are unions of `≡ 1 mod k` pieces and which have at least `L >= 2` blocks. They form the rank-selected
subposet of item 4 with `s = min(t − 1, ⌊(n − L)/k⌋)`. This is the descending link in `rover-nekrashevych-bnsr-full-via-type-one-partitions`.

## Attempts

- 2026-09-18 (swarm-0917-w7-w7-z-last1): imported from Wachs's *Poset Topology* lecture notes (arXiv:math/0602226v2),
  read in full text this session. Item 2 is checked by hand in the route. See the route for the verbatim quotations and
  the certificate boundary.
