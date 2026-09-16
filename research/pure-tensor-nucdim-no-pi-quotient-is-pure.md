---
rg: 2
id: pure-tensor-nucdim-no-pi-quotient-is-pure
kind: claim
title: A pure algebra tensored with a separable finite-nuclear-dimension algebra is pure when no quotient of the product has a compact properly infinite Cuntz class
distinct_from:
  stw95-transfinite-ash-layered-factor-preserves-purity: that requires the second factor to be ASH-layered and puts the simplicity or residual stable finiteness hypothesis on the pure factor; this allows any separable second factor of finite nuclear dimension but puts the no-compact-properly-infinite hypothesis on the quotients of the tensor product.
  stw95-nonunital-ash-factor-preserves-purity: that is the Seth--Vilalta ASH local theorem; this replaces subhomogeneity by finite nuclear dimension through order zero approximations.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be a pure C*-algebra (no separability, exactness or nuclearity
assumed) and let `B` be a separable C*-algebra with `dim_nuc B <= m`.  Put
`C = A tensor_min B`.  Assume that for every closed two-sided ideal `J` of `C`,
the Cuntz semigroup `Cu(C/J)` contains no nonzero element `z` with `z << z` and
`2z <= z`.  Then `C` is pure.  Moreover every `x' << x` in `Cu(C)` admits
`y_0, y_1` with `y_0 + y_1 <= x` and `x' << L y_0, L y_1` for `L = 32(m+1)^3`.

When `B` is also pure this is a positive class for Problem XCV.  The
hypothesis excludes, for instance, properly infinite projections in any
quotient of `C`; how to verify it from conditions on `A` and `B` separately is
not addressed here.
