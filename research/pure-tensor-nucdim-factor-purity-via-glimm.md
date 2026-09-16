---
rg: 2
id: pure-tensor-nucdim-factor-purity-via-glimm
kind: route
title: Purity of the product follows from its Global Glimm Property
target: pure-tensor-nucdim-factor-is-pure
requires:
  - pure-tensor-nucdim-factor-pure-iff-global-glimm
  - pure-tensor-nucdim-factor-has-global-glimm
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be pure and `B` separable with `dim_nuc B <= m`.  By
`pure-tensor-nucdim-factor-has-global-glimm`, `A tensor_min B` has the Global
Glimm Property, and by the implication 2 implies 1 of
`pure-tensor-nucdim-factor-pure-iff-global-glimm` it is pure.
