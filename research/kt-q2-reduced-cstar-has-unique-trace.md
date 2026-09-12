---
rg: 2
id: kt-q2-reduced-cstar-has-unique-trace
kind: claim
title: The binary Kun--Thom double has trivial amenable radical and unique reduced trace
distinct_from:
  kt-double-reduced-cstar-is-mf: that asks for a norm-matrix-corona embedding of the reduced algebra; this proves only that any tracial state on that algebra must be the canonical one.
  reduced-amalgam-canonical-trace-is-mf: that asks for operator-norm asymptotic maps selecting the canonical trace; uniqueness selects a trace after an MF embedding exists but does not create that embedding.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

For `r,d>=3`, put

```text
Gamma=EL_r(F_2[x_1,...,x_d]),
G=EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
D=G *_Gamma G.
```

Then the amenable radical of `D` is trivial.  Consequently `C*_r(D)` has a
unique tracial state, its canonical regular trace.

DERIVATION
kt-q2-bass-serre-unique-trace-proof
