---
rg: 2
id: fpbs-tree-projected-cayley-graphs-strict-thresholds
kind: claim
title: Tree-projected Cayley graphs of cyclic-by-free groups have strict thresholds
root: true
distinct_from:
  fpbs-product-every-generating-set: that asks for every generating set of a direct product; this asks only for generating sets projecting into a free basis of the free quotient, but allows arbitrary height decorations and non-split cyclic-by-free groups.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that covers tree factors with product generating sets through a nonunimodular automorphism group; with asymmetric height decorations no such subgroup is known, so these graphs are outside it.
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
theorem. Symmetric, label-independent height decorations give a nonunimodular
automorphism group and are covered by Hutchcroft arXiv:1711.02590. Asymmetric
decorations such as `{(a,0),(a,1),(b,0),(1,1)}` are not covered by it, as far as
checked. The fibres are cut sets, which gives an exact criterion.

## Attempts

* **Critical fibre-sphere bubble.** Route
  `fpbs-tree-projected-via-critical-sphere-bubble` reduces the claim to
  `fpbs-tree-projected-critical-sphere-bubble-below-one`, which is equivalent to
  the L2 gap on these graphs. **Where it stops:** that critical estimate is open.
* **Nonunimodular structure.**
  * *Covered case.* `fpbs-tree-projected-translate-symmetric-nonunimodular`
    settles the subclass of `F_n x Z` in which every decoration set is a translate
    of one set `D` with `c - D = D`. Examples: `{(a,0),(a,1),(b,0),(b,1),(1,1)}`
    and `{(a,0),(a,1),(b,5),(b,6)}`. Every tree automorphism lifts with a height
    potential, and the lifted end stabilizer is closed, transitive and
    nonunimodular. The earlier note here, that automorphisms "reduce to the free
    group itself", holds only for automorphisms preserving labels and
    orientations.
  * **Where it dies:** when decoration sets differ in shape, as in
    `{(a,0),(a,1),(b,0),(1,1)}` with `D_a = {0,1}` and `D_b = {0}`, only
    color-preserving tree automorphisms lift. Within those, the stabilizer of an
    end has infinitely many orbits, one for each color word of the ray to the
    end, so it is not quasi-transitive. This is not a proof that no other
    nonunimodular subgroup of `Aut(X)` exists.
* **Large rank.** `fpbs-tree-projected-large-rank-strict-thresholds` settles the
  claim whenever `v + 2 m sqrt(2n-1) < 2n-1`, where `v` counts the vertical
  generators and `m` is the largest multiplicity over a letter. It uses the tree
  lift `p_c <= 1/(2n-1)` and a Schur-block adjacency norm. Examples: `n >= 5` for
  one decoration per letter, `n >= 11` for two.
  **Where it stops:** rank two is out of reach of this criterion, even for
  `T_4 □ Z`, where `p_c ||A|| ≈ 1.16`. The asymmetric example
  `(a,0),(a,1),(b,0),(1,1)` stays open.
* **Relative susceptibility.** `fpbs-bs-iff-finite-relative-susceptibility`
  applies with `H` central or normal cyclic. By
  `fpbs-relative-susceptibility-tube-excursion-bound`, divergence can only come
  from far excursions. **Where it stops:** finiteness just above `p_c` is open.
