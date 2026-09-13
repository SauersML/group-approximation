---
rg: 2
id: product-of-tree-groups-has-factorwise-howe-moore
kind: claim
title: In a product of two boundary-2-transitive simple tree groups, representations without factor-invariant vectors have vanishing coefficients
distinct_from:
  howe-moore-property-for-simple-lie-and-p-adic-groups: that imports the Howe-Moore property for simple groups, including single tree groups; this is the factorwise decay for a product of two tree groups, which is not Howe-Moore since each factor fixes the functions on the quotient by the other
artifacts:
  - research/artifacts/product-tree-mixing-transfer-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Call `G` a *boundary-2-transitive simple tree group* if
it is a closed, topologically simple subgroup of `Aut(T)` acting 2-transitively on
`∂T`, for a bi-regular tree `T` of valence at least `3` (for example `Aut(T_d)^+`,
`d >= 3`). Let `G_1`, `G_2` be such groups and `(π, ℋ)` a unitary representation of
`G_1 × G_2` with no nonzero `G_1`-invariant vector and no nonzero `G_2`-invariant
vector. Then all matrix coefficients of `π` vanish at infinity on `G_1 × G_2`.

**Corollary.** A p.m.p. action of `G_1 × G_2` that is ergodic for `G_1` and for `G_2`
separately is mixing, and so is its restriction to any discrete subgroup.

The proof runs Ciobotaru's criterion (arXiv:1403.0223v2, Lemmas 2.9, 2.13, 3.1,
Lemma 4.7 and Corollary 4.18, read from the PDF) on the product: along a sequence
`(a_1^(m_n), a_2^(l_n)) → ∞` one coordinate escapes, its contraction groups generate
that factor, and the normal weak limit of Lemma 3.1 produces a vector invariant under
that factor. Proof in `product-of-tree-groups-factorwise-howe-moore-proof`.
