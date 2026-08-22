---
rg: 2
id: leavitt-eight-cell-curvature-proof
kind: route
title: Reduce eight vertices to five bipartite cubic cores and check their shortest mixed boundaries
target: leavitt-even-region-short-atlas-has-area-ten
requires:
  - leavitt-short-atlas-does-not-close-six-cells
---

For a cubic spherical ribbon graph with `V=8`, Euler gives `E=12,F=6`
and

```text
sum_(faces f)|f|=24.                                     (ECP1)
```

Normal forms in
`Q=V_4(h_0,h_2)*V_4(k_0,k_1)*F(h_1,k_2)` show that every trivial
coefficient word has even length.  Five internal trivial regions and
`(ECP1)` therefore force the outer region to have even length.  A connected
plane graph is bipartite iff every face boundary has even length, so the
core is a cubic bipartite multigraph with color classes of size four.

Write its adjacency matrix with multiplicity.  Row and column sums are
three.  Composition enumeration modulo `S_4 x S_4` gives twelve matrices;
connected planarity leaves the following five representatives:

```text
0012/0111/1110/2100
0012/0111/1200/2010
0012/0120/1200/2001
0012/0210/1101/2010
0111/1011/1101/1110.                                    (ECP2)
```

There are respectively `8,8,8,8,1` planar rotation systems after fixing
global reflection.  Their face-length partitions are

```text
(2,2,4,4,4,8), (2,2,4,4,6,6);
(2,2,2,4,6,8);
(2,2,2,2,8,8);
(2,2,2,6,6,6);
(4,4,4,4,4,4).                                         (ECP3)
```

For each rotation system, orient the twelve edges.  A positive relator
vertex must have two positive and one negative `z` occurrence, and a
negative vertex the reverse; this determines the occurrence slots from the
edge orientation.  Reject immediate inverse-relator dipoles, assign the two
relator colors, and reduce the six region words in `Q`.  There are `531804`
reduced sign- and color-compatible maps and none has five trivial regions.

The nearest maps have four trivial regions.  Their shortest remaining
region labels form 36 oriented words, all of `Q`-length eight.  Substitute

```text
h_0=a_0, h_2=e_0, h_1=q_0p_1,
k_0=a_1, k_1=q_1, k_2=p_0e_1.
```

Split each expanded word into maximal `G_0/G_1` syllables.  Using
`q^2=a^2=e^2=1` and `[a,e]=[a,q]=[e,q]=1`, the 36 cases reduce, up to
cyclic rotation and inversion, to alternating words with every syllable
nonidentity.  (The shortest recurring block is
`h_0h_1^(-1)h_2h_1=a_0p_1^(-1)e_0p_1`.)  Free-product normal form makes
every residual nontrivial.  This proves the claim.

