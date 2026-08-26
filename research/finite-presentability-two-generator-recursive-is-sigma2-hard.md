---
rg: 2
id: finite-presentability-two-generator-recursive-is-sigma2-hard
kind: claim
title: Finite presentability of a two-generator recursively presented group is Sigma-zero-two hard and Sigma-zero-three
distinct_from:
  shift-raag-family-classifies-amenability: that decides amenability of the shift right-angled Artin family; this decides its finite presentability, by Bieri--Strebel rather than by the complete-graph criterion.
  residual-finiteness-two-generator-recursive-is-pi3-complete: that is a third-level completeness theorem on the same family; this is a lower bound one level down for a different property, with the exact level left open.
---

ESTABLISHED.  For two-generator recursive presentations,

```text
FP_rec2  is Sigma^0_2-hard and in Sigma^0_3.                            (FP1)
```

The hardness family is `G_J = < a, t | [a, t^j a t^-j] = 1, j in J >`:

```text
G_J is finitely presentable   iff   J is finite.                        (FP2)
```

Upper bound: "some finite subset of the enumerated relators has every
enumerated relator in its normal closure" is `exists forall exists`.
Whether `FP_rec2` is `Sigma^0_3`-complete is open here; a family in which
adding relators makes infinitely many earlier relators redundant would be
needed, which shift-invariant right-angled Artin families cannot do since
their relators are independent.
