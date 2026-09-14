---
rg: 2
id: simple-ring-with-matrix-units-el-lef-iff-matricial-proof
kind: route
title: Simplicity makes the matrix-unit idempotent full, so one LEF elementary group gives a LEF ring, which is exactly matricial over finite fields
target: simple-ring-with-matrix-units-el-lef-iff-matricial
requires:
  - el-lef-with-full-matrix-units-forces-lef-ring
  - simple-lef-rings-are-exactly-matricial
  - exactly-matricial-rings-have-lef-general-linear-groups
---

Let `R` be countable, simple and unital, with 2x2 matrix units `ε_ij` and `ε_11 != 0`.

- **(1) ⇒ (2).** `R ε_11 R` is a nonzero two-sided ideal, so it equals `R`. Then
  `el-lef-with-full-matrix-units-forces-lef-ring` makes `R` a LEF ring.
- **(2) ⇒ (3).** `simple-lef-rings-are-exactly-matricial`, for a countable simple LEF ring.
- **(3) ⇒ (4).** A unital embedding over finite fields is in particular one over fields, so
  `exactly-matricial-rings-have-lef-general-linear-groups` makes every `GL_N(R)` LEF, and so are its subgroups
  `EL_N(R)`.
- **(4) ⇒ (1).** Take `N = 2`. ∎
