---
rg: 2
id: gkm-rational-twists-have-hirsch-nuclear-dimension
kind: claim
title: Rational twists of finitely generated virtually abelian groups have Hirsch nuclear dimension
distinct_from:
  stw99-problem-lxxxiv-nuclear-dimension-amenable-groups: that asks for a classification of all countable amenable groups and their untwisted group C-star algebras; this is an exact computation for rationally twisted algebras of finitely generated virtually abelian groups.
  stw84-locally-virtually-abelian-uniform-rank: that internal theorem treats untwisted algebras of possibly infinitely generated locally virtually abelian groups; this theorem permits a rational 2-cocycle but assumes finite generation and virtual abelianness.
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Let `G` be a finitely generated virtually abelian discrete group and let
`[sigma] in H^2(G,T)` be rational.  Equivalently in this setting, `[sigma]`
has a cocycle representative whose values are roots of unity.  Then

```text
dim_nuc C*(G,sigma) = h(G),
```

where `h(G)` is the rank of any finite-index abelian subgroup of `G`.

The conclusion concerns the full twisted group C-star algebra.  Since `G` is
amenable, this agrees with the reduced twisted algebra, but no assertion is
made for irrational twists or for general amenable groups.
