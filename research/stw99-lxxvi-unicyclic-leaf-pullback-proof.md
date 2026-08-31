---
rg: 2
id: stw99-lxxvi-unicyclic-leaf-pullback-proof
kind: route
title: Retain the circle class while attaching every forest edge one-endedly
target: stw99-lxxvi-unicyclic-enriched-cu-classification
requires:
  - stw99-lxxvi-finite-tree-formation-preserves-cu-regularity
  - stw99-lxxvi-circle-formation-preserves-cu-regularity
  - stw99-lxxvi-circle-projections-cancel
  - stw99-lxxvi-finite-graph-compact-clutching-rigidity
artifacts:
  - research/artifacts/stw99-lxxvi-unicyclic-enriched-cu-audit-2026-08-31.md
---

For any compact old base `Y` and one interval attached at `v`, restriction
induces

```text
Cu(C(Y union_v [0,1],D))
 ~= Cu(C(Y,D)) pullback_{Cu(D)} Cu(C([0,1],D)).            (1)
```

Surjectivity is Antoine--Perera--Santiago, Theorem 3.3(i): endpoint
evaluation on the new interval is surjective and the interval Cu evaluation
is an order embedding by Antoine--Dadarlat--Perera--Santiago, Theorem 2.6.

For order reflection, begin with genuine comparisons in the actual old-base
and interval coordinates. Stable rank one aligns their comparison vectors
at the gluing fiber. Propagate the alignment unitary along the new edge. If
the target support reaches the free endpoint, it has no prescribed terminal
value. If the support dies first, splice the comparison vectors where their
norm tends to zero. The one-ended estimate preserves the hereditary right
ideal and makes the source-square error arbitrarily small. No pointwise
order embedding on `Cu(C(Y,D))` and no null-homotopy of the endpoint unitary
are used. This proves (1), naturally for coefficient maps.

A connected unicyclic graph is its unique core circle `Gamma` with finitely
many rooted tree edges attached. Iterate (1), use the interval formula, and
use

```text
Lsc(Y union_v [0,1],S)
 ~= Lsc(Y,S) pullback_S Lsc([0,1],S).
```

Associativity of fiber products gives

```text
Cu(C(X,D))
 ~= Cu(C(Gamma,D))
      pullback_{Lsc(Gamma,S)}
    Lsc(X,S).                                              (2)
```

The circle theorem splits its first factor as
`V(C(Gamma,D)) disjointUnion Lsc_nc(Gamma,S)`. The compact graph calculation
identifies a nonzero constant compact fiber `p` with projection bundles
indexed by `K_1(Her(p))=K_1(D)`; simplicity makes `Her(p)` full. Every other
circle evaluation has one preimage, and zero has only the zero bundle. This
proves the exact fiber and pointwise-isomorphism statements.

For a simple stably finite pure coefficient, the actual first-factor map is
an isomorphism on the circle factor by
`stw99-lxxvi-circle-formation-preserves-cu-regularity` and on every `Lsc`
factor by pointwise application of the coefficient Cu-isomorphism. Naturality
of (2) makes it an isomorphism on every unicyclic component. The finite-tree
theorem and finite direct sums complete the pseudoforest corollary; purity is
the separate Seth--Vilalta input.
