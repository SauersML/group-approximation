---
rg: 2
id: kemperman-torsion-free-product-sets-grow
kind: claim
title: In a torsion-free group every product of two finite nonempty sets has at least |B| + |C| - 1 elements
---

**ESTABLISHED** (import) by `kemperman-torsion-free-product-sets-grow-citation`.

**Statement.** Let `G` be a torsion-free group and let `B, C` be finite nonempty subsets of `G`. Then

```text
|BC| >= |B| + |C| - 1,        BC = { bc : b in B, c in C }.
```

This is Kemperman's theorem (J. H. B. Kemperman, On complexes in a semigroup, Indag. Math. 18
(1956), 247-254), the torsion-free Cauchy-Davenport inequality.

**Form used in this graph.** Put `B = Gamma ∪ {e}` with `e notin Gamma`. Then
`(Gamma ∪ {e})C = Gamma C ∪ C`, so

```text
|Gamma C \ C| >= |Gamma|        for every finite Gamma ⊆ G \ {e} and finite nonempty C.
```

Used by `torsion-free-single-defect-rules-need-strict-linear-parts-proof`.
