---
rg: 2
id: fpbs-tree-projected-reversible-letter-nonunimodular
kind: claim
title: Tree-projected Cayley graphs of F_n x Z with one decoration set symmetric up to translation have strict thresholds
distinct_from:
  fpbs-tree-projected-translate-symmetric-nonunimodular: that needs every decoration set to be a translate of one symmetric set and lifts every tree automorphism to a transitive group; this needs one letter whose decoration set is symmetric up to translation and lifts a group with three vertex orbits that keeps the orientation of every other letter.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is Hutchcroft's graph-level theorem for graphs whose automorphism group has a quasi-transitive nonunimodular subgroup; this constructs such a subgroup for tree-projected Cayley graphs with one reversible letter.
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root for every tree-projected generating set of a cyclic-by-free group; this settles the split case whenever some decoration set is symmetric up to translation.
  fpbs-tree-projected-large-rank-strict-thresholds: that proves strict thresholds for large rank with arbitrary decorations through the adjacency norm; this works in rank two, including {(a,0),(a,1),(b,0),(1,1)}, but needs one reversible letter.
---

**ESTABLISHED.** Let `Gamma = F_n x Z` with `n >= 2` and free basis `B`, and
let `pi : Gamma -> F_n` be the projection. Let `S` be a finite symmetric
generating set with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`, and for `s in B` put
`D_s = {k in Z : (s,k) in S}`. Each `D_s` is nonempty, because `pi(S)` generates
`F_n`.

Suppose some letter `s_0 in B` has `c - D_(s_0) = D_(s_0)` for an integer `c`.
Then `Aut(Cay(Gamma,S))` has a closed, quasi-transitive (three vertex orbits),
nonunimodular subgroup. Hence, by Hutchcroft arXiv:1711.02590 Theorem 1.2,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

The other decoration sets are arbitrary.

**Every set of one or two heights qualifies:** `{k}` with `c = 2k`, and `{k,l}`
with `c = k + l`. So the claim covers every tree-projected generating set of
`F_n x Z` in which some letter carries at most two heights.

**Examples.**
* `{(a,0),(a,1),(b,0),(1,1)}` in `F_2 x Z`, with `s_0 = b`, or with `s_0 = a` and
  `c = 1`. This was the smallest example recorded as open in
  `fpbs-tree-projected-cayley-graphs-strict-thresholds`.
* `{(a,0),(a,1),(a,3),(b,0),(1,1)}`, where `D_a` is symmetric under no
  translation.
* `{(a,0),(a,1),(a,3),(b,2),(b,7)}`, with no vertical generator.

**Not covered.**
* Generating sets in which no decoration set is symmetric up to translation, e.g.
  `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,3),(1,1)}`. The construction then has no
  letter it may reverse.
* Non-split cyclic-by-free groups.

**Mechanism.** Take the covering tree of an edge-indexed graph on three vertices
`u, w, x`:
* the `s_0`-edges `u–w` and `w–x` carry indices `2:1` and `1:2`;
* every other letter runs around a directed triangle `u -> w -> x -> u` with
  indices `1:1`.

The automorphisms of this tree that preserve the covering map form a closed
group with three orbits. Its modular value is `1/2` around the cycle "an
`o`-edge from `u` to `w`, then the `s_0`-edge back to `u`". These automorphisms
never reverse a letter other than `s_0`. So every one of them lifts to
`Cay(Gamma,S)`, with a height potential that shifts by `-c` across each reversed
`s_0`-edge.

Proof: `fpbs-reversible-letter-nonunimodular-proof`. Novelty was checked only
against Cairn.
