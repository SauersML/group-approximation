---
rg: 2
id: sl3-re-coefficient-elimination-proof
kind: route
title: Remove the Connes-embeddable lattice coefficient using Gao Proposition 2.2
target: sl3-re-over-lattice-iff-re-over-scalars
requires: []
artifacts:
  - research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md
---

Gao Proposition 2.2 states two permanence facts for `RE/N_1`:

1. if `N_1` tracially embeds into an ultrapower of
   `R tensor N_2`, then `RE/N_1` implies `RE/N_2`;
2. in particular, if `N_1` is QWEP, then `RE/N_1` implies relative
   embeddability over the scalar algebra.

For `N=L(SL_3(Z))`, residual finiteness of `SL_3(Z)` gives Connes
embeddability of `N`, hence QWEP.  Applying item 2 proves

```text
RE/N  =>  RE/C_scalar.
```

For the reverse implication use item 1 with the canonical scalar inclusion
`C_scalar subset N` (equivalently the explicit coefficient-enlargement
clause following Proposition 2.2).  This proves `(RCE1)`.

