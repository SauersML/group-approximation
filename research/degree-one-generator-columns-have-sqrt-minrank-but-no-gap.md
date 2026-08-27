---
rg: 2
id: degree-one-generator-columns-have-sqrt-minrank-but-no-gap
kind: claim
title: Degree-one generator columns force square-root exact minrank but have no robust gap
distinct_from:
  bounded-degree-partial-matrices-have-constant-completion-rank: that permits independent vector labels at repeated occurrences and gives constant rank; this uses exact additive laws to identify repeated columns and thereby forces a triangular matrix block.
  sparse-generator-column-sampling-has-bilinear-kernel: that proves every sparse sampler misses some full-table bilinear twist but does not bound the affine completion rank; this computes an explicit sparse fiber with rank tending to infinity.
  bounded-incidence-generator-column-minrank-witness: that asks for both growing exact rank and fixed-threshold HS robustness; this supplies the first property and sharply refutes the second for the construction.
---

There are asymptotically good generator-column multisets of length `Theta(n)`
and sampled bipartite graphs of maximum degree one whose affine completion
rank is

```text
r(E)=Theta(sqrt(n)).                                         (DGM1)
```

Fix `r` with `r(r+1)/2<=n`.  Start with any length-`Theta(n)` binary
generator matrix of dimension `n` and relative distance bounded below.  To
each of its two column multisets append, for every `1<=p<=q<=r`, one private
left column

```text
a_(p,q)=e_p
```

and one private right column

```text
b_(p,q)=e_q.
```

Join only the matching pair of private occurrences.  Every occurrence has
degree one.  The ideal sign on that edge is `delta_(p,q)`, so a bilinear form
`B` passes all tests exactly iff

```text
B_(p,q)=delta_(p,q)                 (1<=p<=q<=r).       (DGM2)
```

The leading `r`-square block is lower triangular with diagonal one and hence
has rank at least `r`.  Taking that block to be the identity and all other
entries zero attains rank `r`.  Thus `(DGM1)` holds exactly.  Appending only
`O(n)` columns preserves a constant relative distance, hence the uniform
generator-column spectral constants.

This exact witness has no dimension-independent robust soundness.  Under the
uniform edge distribution, the zero bilinear form violates only the `r`
diagonal-one constraints among `r(r+1)/2` tests, a fraction

```text
2/(r+1)->0.                                                  (DGM3)
```

The corresponding one-dimensional trivial X/Z representation therefore has
vanishing loss.

Repeating diagonal tests until they have fixed positive density does not
repair the construction.  Partition `{1,...,r}` into `k` blocks and let `B`
be the block-diagonal matrix whose blocks are all-one matrices.  It has rank
at most `k`, satisfies every diagonal constraint, and violates an
off-diagonal zero constraint only when its two indices lie in one block.
For balanced blocks that fraction is at most `1/k+o(1)`.  Thus for every
fixed error threshold `epsilon>0`, a rank-`O(1/epsilon)` exact additive Weyl
model passes at loss below `epsilon`, independently of `r`.

The construction proves that additive laws genuinely defeat the unrestricted
constant-rank completion lemma, but also that growing exact minrank alone is
far too weak.  The open robust witness must make the ideal affine syndrome a
constant relative distance from every bounded-rank completion, not merely
exclude exact bounded-rank completions.
