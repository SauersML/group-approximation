---
rg: 2
id: fpbs-tree-projected-letter-exchange-nonunimodular
kind: claim
title: Tree-projected Cayley graphs of F_n x Z in which two letters carry translated or reflected decoration sets have strict thresholds
distinct_from:
  fpbs-tree-projected-reversible-letter-nonunimodular: that needs one decoration set symmetric up to translation and lifts a group reversing that letter; this needs two letters whose decoration sets agree up to translation and reflection, lifts a group that exchanges them and keeps every orientation, and so covers sets in which no decoration set is symmetric.
  fpbs-tree-projected-translate-symmetric-nonunimodular: that needs every decoration set to be a translate of one symmetric set and lifts every tree automorphism; this allows asymmetric shapes and lifts only orientation-preserving exchanges of two letters.
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root for every tree-projected generating set of a cyclic-by-free group; this settles the split case whenever two decoration sets agree up to translation and reflection.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is Hutchcroft's graph-level theorem for graphs whose automorphism group has a quasi-transitive nonunimodular subgroup; this constructs such a subgroup for a new class of tree-projected Cayley graphs.
artifacts:
  - research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py
  - research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma = F_n x Z` with `n >= 2`, free basis `B`, and
projection `pi : Gamma -> F_n`. Let `S` be a finite symmetric generating set with
`pi(S) ⊆ {1} ∪ B ∪ B^(-1)`, and put `D_s = {k in Z : (s,k) in S}` for `s in B`.
Suppose two distinct letters `s, t in B` satisfy, for some integer `c`,

```text
D_t = D_s + c      or      D_t = c - D_s.
```

Then `Aut(Cay(Gamma,S))` has a closed nonunimodular subgroup with three vertex
orbits. Hence, by Hutchcroft arXiv:1711.02590v3 Theorem 1.2,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

The other decoration sets and the vertical generators are arbitrary.

**Examples.**
* `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,3),(1,1)}` in `F_2 x Z`, with
  `D_a = D_b = {0,1,3}`. No decoration set is symmetric up to translation. This
  set was recorded as not covered in
  `fpbs-tree-projected-reversible-letter-nonunimodular` and in the root.
* `{(a,0),(a,1),(a,3),(b,0),(b,2),(b,3),(1,1)}`, with `D_b = 3 - D_a`.
* `{(a,0),(a,2),(a,7),(b,1),(b,6),(b,8)}`, with `D_b = 8 - D_a` and no vertical
  generator. It generates: `(a,2)(a,0)^(-1) = (1,2)` and `(a,7)(a,2)^(-1) = (1,5)`
  give the centre, since `gcd(2,5) = 1`.

**What the lifted-tree method now covers.** With
`fpbs-tree-projected-reversible-letter-nonunimodular`: a closed quasi-transitive
nonunimodular subgroup exists whenever some decoration set is symmetric up to
translation, or two decoration sets agree up to translation and reflection.
Only *rigid* decorations remain, in which the `2n` oriented shapes `D_s`, `-D_s`
are pairwise distinct up to translation. For the rigid example
`{(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}`, Section 3 of
`research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md` shows that the
whole automorphism group is discrete, so Hutchcroft's theorem cannot apply there.

**Mechanism.** Take the covering tree of an edge-indexed *directed* graph on three
vertices `u, w, x`, with five exchange edges
`u->w (2:1), w->x (1:2), x->w (1:1), x->u (1:1), w->u (1:1)` and, for every other
letter, a directed triangle `u->w->x->u` with indices `1:1`. Every vertex of the
tree has two outgoing and two incoming exchange edges, so labelling them `s` and
`t` identifies the tree with `Cay(F_n,B)`. The index-preserving automorphisms
keep every orientation but may exchange `s` with `t`. They lift with a height
potential that shifts by `c` across each exchanged edge, and their modular ratio
around `w -> x -> w` is `1/2`.

Proof: `fpbs-letter-exchange-nonunimodular-proof`. Novelty was checked only
against Cairn.
