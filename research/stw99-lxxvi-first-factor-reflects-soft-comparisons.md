---
rg: 2
id: stw99-lxxvi-first-factor-reflects-soft-comparisons
kind: claim
title: The first-factor map reflects every soft Cuntz comparison
distinct_from:
  stw99-lxxvi-first-factor-map-has-identical-coarse-shadows: that identifies ideals, K-theory and quasitraces but warns that these data do not classify arbitrary Cuntz elements; this theorem uses softness and almost unperforation to turn the ideal and quasitrace shadows into actual order reflection.
  stw99-lxxvi-stable-weak-cancellation-finite-compact-injectivity: that prevents collapse of compact projection classes under stable weak cancellation and finiteness; this handles the complementary soft part and requires neither projections nor cancellation.
  stw99-lxxvi-external-cu-tensor-map-isomorphism: that asks for invertibility on the entire Cuntz semigroup of every pure algebra; this proves only order reflection when the left-hand source class is soft and makes no surjectivity assertion.
artifacts:
  - research/artifacts/stw99-lxxvi-soft-comparison-audit-2026-08-30.md
---

**ESTABLISHED SOFT ORDER-REFLECTION THEOREM.**  Let `A` be a separable
C-star algebra such that `Cu(A)` is almost unperforated, and write

```text
phi = Cu(iota_A):Cu(A) -> Cu(A tensor_min Z).
```

Call `x in Cu(A)` functionally soft when

```text
for every x' << x there is k>=1 with (k+1)x' <= kx.          (SC1)
```

If `x` is functionally soft and `y` is arbitrary, then

```text
phi(x) <= phi(y)   implies   x <= y.                          (SC2)
```

Consequently `phi` is an order embedding on the subsemigroup of functionally
soft elements.  In particular, for every separable pure `A`, any failure of
order reflection has a nonsoft left-hand class, and any pair collapsed by
`phi` cannot consist of two soft classes.

Thus the compact-cancellation and infinite-projection corridors in the
current LXXVI graph do not exhaust the obstruction, but the remaining
noncompact corridor is sharply restricted: equal ideals and equal ranks can
fail to determine a class only through nonsoft gluing.  No stable-rank-one,
finiteness, exactness, or geometric-base hypothesis is used.

DERIVATION
stw99-lxxvi-soft-comparison-reflection-proof
