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
* **Nonunimodular structure.** For asymmetric or label-dependent height sets,
  tree automorphisms preserving labels, orientations and height sets reduce to
  the free group itself. **Where it dies:** there is no nonunimodular
  quasi-transitive subgroup to use.
* **Relative susceptibility.** `fpbs-bs-iff-finite-relative-susceptibility`
  applies with `H` central or normal cyclic. By
  `fpbs-relative-susceptibility-tube-excursion-bound`, divergence can only come
  from far excursions. **Where it stops:** finiteness just above `p_c` is open.
