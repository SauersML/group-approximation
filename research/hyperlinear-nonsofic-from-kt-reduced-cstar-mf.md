---
rg: 2
id: hyperlinear-nonsofic-from-kt-reduced-cstar-mf
kind: route
title: Reduced MF of the q=2 Kun--Thom double gives the separation
target: hyperlinear-nonsofic-group
requires:
  - kt-double-reduced-cstar-is-mf
  - kt-pair-group-double-is-nonsofic
---

Let `D=G *_Gamma G` be the explicit `q=2` Kun--Thom double.  By
`kt-double-reduced-cstar-is-mf`, choose an embedding

```text
C*_r(D) -> product_n M_(d_n) / direct_sum_n M_(d_n).
```

Compose with the quotient to a tracial matrix ultraproduct.  The pullback of
its trace is a tracial state on `C*_r(D)`, hence is the canonical trace by the
unique-trace theorem recorded in `notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md`.
That trace is faithful, so the composite is injective and extends to a
trace-preserving embedding of `L(D)` into `R^omega`.  Thus `D` is
hyperlinear.  The second prerequisite says the same explicit group is not
sofic.

