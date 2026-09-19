---
rg: 2
id: stw95-inner-cofinal-cu-image-gives-almost-divisibility
kind: claim
title: Inner cofinality of the external Cu image transfers almost divisibility
distinct_from:
  split-cu-tensor-map-implies-pure-product: that assumes a Cu-morphism right inverse and transfers both purity axioms; this claim assumes only inner cofinality and concludes almost divisibility alone.
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
---

Let `A,B` be pure, set `S=Cu(A) tensor_Cu Cu(B)` and
`T=Cu(A tensor_min B)`, and let `theta:S->T` be canonical.  Suppose that for
every `x'<<x` in `T` there are `a'<<a` in `S` such that

```text
x' <= theta(a'),     theta(a) <= x.
```

Then `T` is almost divisible.
