---
rg: 2
id: block-escape-relocates-nonsoficity
kind: claim
title: Orbit resolution fails only through invariant blocks, and every such escape inherits the nonsoficity
distinct_from:
  two-site-rigidity-of-lamp-witnesses: that constrains the shape of a lamp-to-lamp witness and puts the defect on the acting part; this settles the combinatorial lemma that was supposed to convert that constraint into an obstruction, and finds it false.
  hilbert-embeddable-witness-for-kun-thom-wreath: that is the open design question; this closes one proposed route to answering it negatively and reports what the route's failure mode is.
  marked-double-coset-infinite-degree: that computes an index in the infinite pair; this is about invariant partitions of the finite site sets and about intermediate subgroups.
---

Let `K` act transitively on a finite site set `Y`, let `O` be a `K`-orbit of
subsets of `Y`, and for a permutation `pi` write `fix_O(pi)` and `fix_Y(pi)`
for the fractions of `O` fixed setwise and of `Y` fixed pointwise.

1. **The resolution lemma is false.**  There is no function `delta` with
   `delta(epsilon) -> 0` such that `fix_O(pi) >= 1-epsilon` implies
   `fix_Y(pi) >= 1-delta(epsilon)`, even for transitive `Y`.  If some
   nontrivial `K`-invariant partition of `Y` has every member of `O` a union
   of blocks, then **every** permutation preserving each block setwise fixes
   **all** of `O`, while moving as many points as the blocks are large.
   Transitivity does not help: it only rules out the degenerate version in
   which `O` ignores a `K`-invariant subset.
2. **Blocks are the only failure at `epsilon = 0`.**  If the indicator
   vectors `1_S`, `S in O`, span `F_2^Y`, then a permutation fixing every
   member of `O` fixes every vector of `F_2^Y` and is the identity.  So a
   total failure of resolution forces the `1_S` into a proper subspace, which
   is `K`-invariant; invariant partitions are the geometric instance of that.
3. **Every block escape relocates the problem and inherits its
   nonsoficity.**  In the Kun--Thom setting the site sets model `X=G/Gamma`,
   and an invariant partition corresponds to an intermediate subgroup
   `Gamma <= H <= G`, with the marked pair still separated exactly when
   `h notin H`.  For any such `H`, the `G`-map `G/Gamma -> G/H` induces

   ```text
   W = (directSum_(G/Gamma) Z/2Z) semidirect G
     -->  W_H = (directSum_(G/H) Z/2Z) semidirect G,
   ```

   carrying the marked involution `w=a_(h Gamma) a_Gamma` to
   `a_(hH) a_H != 1`.  Since `w` lies in the sofic radical of `W`, `W_H`
   cannot be sofic; and by Gao--Kunnawalkam Elayavalli--Patchell a sofic
   underlying action would make `W_H` sofic.  So `G` acting on `G/H` is not
   a sofic action either.

Consequently the proposed obstruction — that a Hilbert embeddable witness
would yield a sofic approximation of the coset action — **does not close as
stated**, because the character condition controls only the orbit of subsets
and not the sites.  But the gap it leaves is not a place where a witness can
comfortably live: any invariant partition that keeps the mark separated
carries the same nonsoficity down to a smaller coset space, so the escape is a
translation of the problem rather than a solution to it.

## Why this sits off the root graph

This is a settled lemma with no consumer, for a structural reason worth
recording.  Its clause 3 generalizes [[coordinate-action-not-sofic]] from the
marked subgroup to every intermediate `Gamma <= H <= G`, and that claim is
itself an established island — proved, consumed by nothing.  So the natural
edge here would run into a node that is already off the root graph, which moves
the detachment rather than removing it.

The lemma earns its place by what it kills: the resolution lemma is FALSE, and
anyone who reaches for orbit resolution to convert
[[two-site-rigidity-of-lamp-witnesses]] into an obstruction will rediscover the
block counterexample.  Clause 3 is the reason the failure is not a way out —
every block escape inherits the nonsoficity, so there is no smaller coset space
where the problem becomes easy.
