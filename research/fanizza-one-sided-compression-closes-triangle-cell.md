---
rg: 2
id: fanizza-one-sided-compression-closes-triangle-cell
kind: route
title: Combine source-full compression with the guarded rank floor
target: single-triangle-trace-cyclic-return-cell
requires:
  - fanizza-matrix-coordinate-source-full-compression
  - fanizza-compressed-unitary-has-guarded-rank-floor
artifacts:
  - research/artifacts/fanizza-one-sided-compressed-rank-floor-2026-08-21.md
---

For a finite microstate of the cell, `(OCR8)` and `(OCR7)` give

```text
1/8-o(1) <= tr(H) <= ||X^*X-E||_2^2 <= omega(def)^2,
```

which is impossible once the defect is sufficiently small.  Hence the cell
has no vanishing-defect finite microstate sequence; in particular all finite
return estimates required by `single-triangle-trace-cyclic-return-cell` hold
below the resulting fixed threshold.  The first prerequisite supplies the
exact countably amplified HALT extension, while its explicitly
matrix-coordinate decoder avoids asserting the partial-isometry equations
in the regular group von Neumann algebra.  Thus the positive mark and the
regular firewall are preserved.
