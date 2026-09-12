---
rg: 2
id: fpbs-tree-projected-translate-symmetric-nonunimodular
kind: claim
title: Tree-projected Cayley graphs of F_n x Z whose decoration sets are translates of one symmetric set have strict thresholds
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is Hutchcroft's graph-level theorem for graphs with a closed quasi-transitive nonunimodular subgroup; this constructs such a subgroup for a class of tree-projected Cayley graphs through height-compensated tree automorphisms.
  fpbs-tree-projected-large-rank-strict-thresholds: that proves strict thresholds for large rank with arbitrary decorations through the adjacency norm; this covers every rank including two, but only decoration sets that are translates of one symmetric set.
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root for every tree-projected generating set; this settles the translate-symmetric subclass and leaves decoration sets of different shapes open.
---

**ESTABLISHED.** Let `Gamma = F_n x Z` with `n >= 2`, free basis `B`, and
`pi : Gamma -> F_n` the projection. Let `S` be a finite symmetric generating set
with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`. For `s in B` put
`D_s = {k in Z : (s,k) in S}`, so `D_(s^(-1)) = -D_s`, and let
`V = {k : (1,k) in S}`.

Suppose there are a finite nonempty `D ⊆ Z` and `c in Z` with `c - D = D`, such
that every `D_s` (`s in B`) is a translate of `D`. Then `Aut(Cay(Gamma,S))`
contains a closed, vertex-transitive, nonunimodular subgroup. Hence, by
Hutchcroft arXiv:1711.02590,

```text
p_c(Cay(Gamma,S)) < p_h <= p_u(Cay(Gamma,S)).
```

**Examples covered (rank two included).**
* `{(a,0),(a,1),(b,0),(b,1),(1,1)}`, where the height set `{0,1}` is not
  symmetric about 0 but is symmetric up to translation.
* `{(a,0),(a,1),(b,5),(b,6)}`: label-dependent offsets, no vertical generator.
* `{(a,0),(a,2),(b,3),(b,5),(1,1)}`.

**Not covered.**
* `{(a,0),(a,1),(b,0),(1,1)}`: `D_a = {0,1}` and `D_b = {0}` have different
  sizes, so no tree automorphism exchanging `a`-edges with `b`-edges lifts.
* Any set such as `D_a = {0,1,3}`, which is symmetric under no translation, so
  orientation reversal of `a`-edges cannot be compensated.

**Correction to the root.** The Attempts of
`fpbs-tree-projected-cayley-graphs-strict-thresholds` said that automorphisms of
asymmetric or label-dependent decorations reduce to the free group. That holds
for automorphisms preserving labels and orientations. Once a height shift is
allowed to vary along the tree, reversing orientations and exchanging letters is
possible exactly when the decoration sets are translates of one symmetric set.

**Mechanism.** Every tree automorphism `phi` lifts to
`Psi(g,n) = (phi(g), n + h_phi(g))`, with `h_phi` a potential for the translation
between `D(e)` and `D(phi e)` on each oriented edge. The lifts of the stabilizer
of an end of the tree form the nonunimodular subgroup: modular ratio `1/(2n-1)`
between a vertex and its parent fibre.

Proof: `fpbs-translate-symmetric-nonunimodular-proof`. Novelty was checked only
against Cairn.
