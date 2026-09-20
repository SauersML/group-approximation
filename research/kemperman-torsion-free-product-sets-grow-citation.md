---
rg: 2
id: kemperman-torsion-free-product-sets-grow-citation
kind: route
title: Import Kemperman's product-set bound for torsion-free groups as quoted by Abdollahi--Jafari
target: kemperman-torsion-free-product-sets-grow
requires: []
---

Source read from the arXiv:1808.08708v3 PDF (A. Abdollahi and F. Jafari, *Cardinality of product
sets in torsion-free groups and applications in group algebras*), 2026-09-19. Section 1 opens:

> Let G be a torsion-free group written multiplicatively, and let |. | denote the cardinality of a
> finite set. One of the basic problems in Additive Number Theory is to obtain lower bounds for the
> cardinality of BC = {bc | b ∈ B, c ∈ C} of two finite subsets B and C in terms of |B| and |C|.
> [...] By the main result of [22],
> (1.1) |BC| ≥ |B| + |C| − 1.

Their reference list:

> [22] J. H. B. Kemperman, On complexes in a semigroup, Indag. Math., 18 (1956), 247-254.

The inequality is stated for finite subsets `B, C` of an arbitrary torsion-free group. It is
trivial or vacuous when one of them is empty, so the target's restriction to nonempty sets loses
nothing.

**Derived form.** With `B = Gamma ∪ {e}`, where `e notin Gamma`, one has
`|B| = |Gamma| + 1` and `BC = Gamma C ∪ C`. So `|Gamma C ∪ C| >= |Gamma| + |C|`, and removing
`C` gives `|Gamma C \ C| >= |Gamma|`.
