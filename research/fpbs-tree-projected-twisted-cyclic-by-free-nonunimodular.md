---
rg: 2
id: fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular
kind: claim
title: Tree-projected Cayley graphs of cyclic-by-free groups with non-central kernel have strict thresholds
distinct_from:
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root for every cyclic-by-free group; this settles every group in it other than F_n x Z, for every decoration, so only F_n x Z remains there.
  fpbs-tree-projected-reversible-letter-nonunimodular: that works in F_n x Z, needs one decoration set symmetric up to translation and lifts with a height potential; this works when the kernel is not central, needs no condition on any decoration set, and lifts with no potential.
  fpbs-tree-projected-letter-exchange-nonunimodular: that works in F_n x Z and needs two decoration sets that agree up to translation and reflection; this needs no relation between decoration sets but only covers groups whose cyclic kernel is not central.
  fpbs-tree-projected-translate-symmetric-nonunimodular: that works in F_n x Z when every decoration set is a translate of one symmetric set; this allows arbitrary decoration sets over a twisted group.
  fpbs-tree-projected-rigid-decorations-discrete-automorphisms: that shows rigid decoration data over F_n x Z give discrete fibre-preserving automorphism groups, one of them discrete outright; this shows the same data over a group with non-central kernel always give a nonunimodular subgroup.
  fpbs-tree-projected-large-rank-strict-thresholds: that covers non-central kernels too, but only when v + 2m sqrt(2n-1) < 2n-1; this covers every rank, including two, and every multiplicity.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is Hutchcroft's graph-level theorem for graphs with a quasi-transitive nonunimodular automorphism subgroup; this constructs such a subgroup for a new class of Cayley graphs.
artifacts:
  - research/artifacts/fpbs-twisted-cyclic-by-free-nonunimodular-2026-09-16.md
  - experiments/fpbs-twisted-cyclic-by-free-2026-09-16/twisted_lift_check.py
---

**ESTABLISHED.** Let `Gamma` be finitely generated, with an infinite cyclic normal
subgroup `H` such that `Gamma/H ≅ F_n`, `n >= 2`. Suppose `H` is **not central**.
Let `B` be a free basis of `F_n`, and let `S` be a finite symmetric generating set
whose image in `F_n` lies in `{1} ∪ B ∪ B^(-1)`. Then `Aut(Cay(Gamma,S))` has a
closed nonunimodular subgroup with four vertex orbits. Hence, by Hutchcroft
arXiv:1804.10191 (`thm:nonunimodular`) and arXiv:1711.02590v3 (Theorem 1.2),

```text
p_c(Cay(Gamma,S)) < p_(2->2)(Cay(Gamma,S))   and   p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

**Normal form.** The extension splits because `F_n` is free. So
`Gamma ≅ Z ⋊_chi F_n` with product `(m,g)(m',g') = (m + chi(g) m', g g')` for a
homomorphism `chi : F_n -> {+1,-1}`, and `H` is central iff `chi = 1`. An
infinite cyclic normal subgroup of `F_n x Z` is central, since `n >= 2`. So the
hypothesis says exactly that `Gamma` is not `F_n x Z`. Then
`S = {(d,s) : s in B, d in D_s} ∪ {(v,1) : v in V}` together with inverses, where
the decoration sets `D_s` and the vertical set `V = -V` are **arbitrary**. Rigid
decorations are included.

**Examples.**
* `Z ⋊ F_2` with `a` acting by `-1` and `b` trivially, and
  `S = {(0,a),(1,a),(3,a),(0,b),(1,b),(4,b),(1,1)}` plus inverses. Over `F_2 x Z`
  the same decoration data give a Cayley graph whose whole automorphism group is
  discrete (`fpbs-tree-projected-rigid-decorations-discrete-automorphisms`).
* Both letters acting by `-1`, with `S = {(0,a),(2,a),(7,a),(1,b),(6,b),(8,b)}` and
  no vertical generator. It generates, since `(2,a)(0,a)^(-1) = (2,1)` and
  `(7,a)(0,a)^(-1) = (7,1)`.

**What is new.** This settles the "non-split groups" bullet of
`fpbs-tree-projected-cayley-graphs-strict-thresholds`, which means the groups
other than `F_n x Z`, for every decoration and every rank. The earlier lifted-tree
results over `F_n x Z` need a symmetry of the decoration sets. Here none is needed.
The root now reduces to rigid decorations over `F_n x Z`
(`fpbs-tree-projected-reduce-to-rigid-decorations`).

**Mechanism.** Colour `g in F_n` by `chi(g)`. Orient the tree edge `{g,gs}` from `g`
if `chi(g) = +1` and from `gs` otherwise. Then the edges of `X = Cay(Gamma,S)` over
it are exactly `(m,p)–(m+d,q)` with `d in D_s`, where `p -> q` is the orientation.
If `chi(s) = -1`, both `s`-edges at a vertex point outward (at a `+` vertex) or both
inward (at a `-` vertex). So a tree automorphism may swap them and still keep every
orientation, and every automorphism preserving labels and orientations lifts as
`(m,g) -> (m+k, phi g)`, with no height potential.

The subgroup preserving the covering map of the covering tree of a four-vertex
edge-indexed graph has modular ratio `1/2`. That graph has vertices `u, w` (`+`)
and `x, y` (`-`), the `s_0`-edges `u–x (2:1)`, `x–w (1:1)`, `w–y (1:2)`, the
4-cycle `u–x–w–y–u` for every other twisted letter, and directed pairs
`u <-> w`, `x <-> y` for untwisted letters. The full group of colour-, label- and
orientation-preserving tree automorphisms is unimodular, so the finer covering
structure is essential.

Proof: `fpbs-twisted-cyclic-by-free-nonunimodular-proof`. Novelty was checked
against Cairn and an arXiv abstract search on 2026-09-16.
