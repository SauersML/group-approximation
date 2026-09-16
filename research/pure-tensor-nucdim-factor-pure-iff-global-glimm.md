---
rg: 2
id: pure-tensor-nucdim-factor-pure-iff-global-glimm
kind: claim
title: A pure algebra tensored with a separable finite-nuclear-dimension algebra is pure iff the product has the Global Glimm Property
distinct_from:
  stw99-problem-lxxiii-global-glimm: that asks whether every nowhere scattered algebra has the Global Glimm Property; this proves that for tensor products of a pure algebra with a separable finite-nuclear-dimension algebra the Global Glimm Property is equivalent to purity.
  pure-tensor-nucdim-no-pi-quotient-is-pure: that proves purity outright under a quotient hypothesis; this is an unconditional equivalence that leaves the Global Glimm Property open.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be a pure C*-algebra and let `B` be a separable C*-algebra with
`dim_nuc B <= m`.  For `C = A tensor_min B` the following are equivalent:

1. `C` is pure;
2. `C` has the Global Glimm Property;
3. there is `L in N` such that every `x' << x` in `Cu(C)` admits `y_0, y_1` with
   `y_0 + y_1 <= x` and `x' << L y_0, L y_1`.
