---
rg: 2
id: stw90-php-times-cstar-simple-is-strict-comparison-proof
kind: route
title: Tensor a completely selfless PHP trace with the unique trace of the second factor
target: stw90-php-times-cstar-simple-is-strict-comparison
requires:
  - complete-selflessness-tensor-permanence
  - ozawa-php-groups-completely-selfless
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Ozawa's PHP theorem makes `(C*_r(P),tau_P)` completely selfless.  Since `H`
is C*-simple, `C*_r(H)` is simple and its canonical trace `tau_H` is its
unique trace.  Complete-selflessness tensor permanence, in the version that
does not require exactness of the second algebra, gives selflessness of

```text
(C*_r(P) tensor_min C*_r(H), tau_P tensor tau_H).
```

The canonical regular representation identifies this tensor product with
`C*_r(P x H)` and the product trace with its canonical trace.  Robert's
tracial regularity theorem then gives strict comparison.

The free group `F_2` has PHP because it is acylindrically hyperbolic with
trivial finite radical, giving the final specialization.

**Trust boundary.**  Ozawa's complete-selflessness theorem, the 2026 tensor
permanence theorem, Robert's strict-comparison consequence, and the standard
unique-trace theorem for C*-simple groups are imported.  The reduced direct
product/tensor-product identification is standard and exactness is not used.
