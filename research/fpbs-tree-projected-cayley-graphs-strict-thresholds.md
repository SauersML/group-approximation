---
rg: 2
id: fpbs-tree-projected-cayley-graphs-strict-thresholds
kind: claim
title: Tree-projected Cayley graphs of cyclic-by-free groups have strict thresholds
root: true
distinct_from:
  fpbs-product-every-generating-set: that asks for every generating set of a direct product; this asks only for generating sets projecting into a free basis of the free quotient, but allows arbitrary height decorations and non-split cyclic-by-free groups.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that covers graphs whose automorphism group has a quasi-transitive nonunimodular subgroup; here such a subgroup is known only when some decoration set is symmetric up to translation or two decoration sets agree up to translation and reflection, and for rigid decorations such as {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)} none exists.
  fpbs-hyperbolic-quotient-every-generating-set: that is the every-generating-set class over any hyperbolic quotient; this is the tree-projected subclass, where fibres are cut sets and an exact finite-radius criterion exists.
---

**OPEN.** Let `Gamma` be finitely generated with an infinite cyclic normal
subgroup `H` such that `Gamma/H ≅ F_n`, `n >= 2`. Let `S` be a finite symmetric
generating set whose image in `F_n` lies in a free basis, its inverses and `1`.
Then

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

*Marked `root` because* this is the smallest open instance of Choi–Seo
arXiv:2508.08932 Question 1.3 (`F_2 x Z`) that is not covered by a cited
theorem. For `F_n x Z`, a single decoration set symmetric up to translation
gives a closed quasi-transitive nonunimodular subgroup, so Hutchcroft
arXiv:1711.02590 applies: `fpbs-tree-projected-reversible-letter-nonunimodular`.
That covers `{(a,0),(a,1),(b,0),(1,1)}` and every set in which some letter
carries at most two heights. Two letters whose decoration sets agree up to
translation and reflection also give one:
`fpbs-tree-projected-letter-exchange-nonunimodular`, covering
`{(a,0),(a,1),(a,3),(b,0),(b,1),(b,3),(1,1)}`. Still open:
* *rigid* decorations, in which the oriented shapes `D_s`, `-D_s` are pairwise
  distinct up to translation, such as
  `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}`. For that set the whole
  automorphism group is discrete (Section 3 of
  `research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md`), so no
  nonunimodular argument exists and a proof must work on unimodular graphs;
* non-split groups.

The fibres are cut sets, which gives an exact criterion.

## Attempts

* **Critical fibre-sphere bubble.** Route
  `fpbs-tree-projected-via-critical-sphere-bubble` reduces the claim to
  `fpbs-tree-projected-critical-sphere-bubble-below-one`, which is equivalent to
  the L2 gap on these graphs. **Where it stops:** that critical estimate is open.
* **Nonunimodular structure.**
  * *Covered case, one symmetric shape.*
    `fpbs-tree-projected-translate-symmetric-nonunimodular` settles the subclass
    of `F_n x Z` in which every decoration set is a translate of one set `D` with
    `c - D = D`. Examples: `{(a,0),(a,1),(b,0),(b,1),(1,1)}` and
    `{(a,0),(a,1),(b,5),(b,6)}`. Every tree automorphism lifts with a height
    potential, and the lifted end stabilizer is closed, transitive and
    nonunimodular. The earlier note here, that automorphisms "reduce to the free
    group itself", holds only for automorphisms preserving labels and
    orientations.
  * *Covered case, one reversible letter.*
    `fpbs-tree-projected-reversible-letter-nonunimodular` settles `F_n x Z`
    whenever some `D_s` satisfies `c - D_s = D_s`, e.g.
    `{(a,0),(a,1),(b,0),(1,1)}`. End stabilizers of color-preserving tree
    automorphisms have infinitely many orbits. The automorphism group of the
    covering tree of a three-vertex edge-indexed graph has three orbits instead,
    reverses only that letter, and has modular ratio `1/2`.
  * *Covered case, two exchangeable letters.*
    `fpbs-tree-projected-letter-exchange-nonunimodular` settles `F_n x Z`
    whenever `D_t = D_s + c` or `D_t = c - D_s` for two letters, e.g.
    `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,3),(1,1)}`. The covering tree of a
    directed edge-indexed graph on three vertices keeps every orientation,
    exchanges the two letters, and has modular ratio `1/2`.
  * **Where it dies:** rigid decorations. When the oriented shapes are pairwise
    distinct up to translation and the vertical part is `{(1,±1)}`, every
    fibre-preserving automorphism lies in the discrete group `Gamma ⋊ Z/2`. For
    `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}`, triangle counts make every
    automorphism fibre-preserving, so `Aut(X)` itself is discrete and unimodular
    (Section 3 of `research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md`).
    Hutchcroft's theorem cannot reach this graph.
* **Large rank.** `fpbs-tree-projected-large-rank-strict-thresholds` settles the
  claim whenever `v + 2 m sqrt(2n-1) < 2n-1`, where `v` counts the vertical
  generators and `m` is the largest multiplicity over a letter. It uses the tree
  lift `p_c <= 1/(2n-1)` and a Schur-block adjacency norm. Examples: `n >= 5` for
  one decoration per letter, `n >= 11` for two.
  **Where it stops:** rank two is out of reach of this criterion, even for
  `T_4 □ Z`, where `p_c ||A|| ≈ 1.16`. The example `(a,0),(a,1),(b,0),(1,1)` is
  settled instead by the reversible-letter construction.
* **Relative susceptibility.** `fpbs-bs-iff-finite-relative-susceptibility`
  applies with `H` central or normal cyclic. By
  `fpbs-relative-susceptibility-tube-excursion-bound`, divergence can only come
  from far excursions. **Where it stops:** finiteness just above `p_c` is open.
