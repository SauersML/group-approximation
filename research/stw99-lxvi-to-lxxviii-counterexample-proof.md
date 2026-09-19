---
rg: 2
id: stw99-lxvi-to-lxxviii-counterexample-proof
kind: route
title: Cut an LXVI witness to its finite CAR seed and apply the finite-target obstruction
target: stw99-lxvi-witness-refutes-lxxviii
requires:
  - stw99-lxvi-iff-finite-car-corner-with-infinite-double
  - stw99-lxvi-finite-seed-has-no-quasitrace
  - stw99-lxxviii-finite-target-obstruction
---

Let `(B,phi)` solve LXVI.  The finite-corner reduction
`stw99-lxvi-iff-finite-car-corner-with-infinite-double` produces a simple
unital C-star algebra `C` such that

```text
1_C is finite,
M_2(C) has infinite unit,
psi:M_(2^infinity) -> C is a unital embedding.
```

The quasitrace obstruction
`stw99-lxvi-finite-seed-has-no-quasitrace` says that `C` has no nonzero
bounded quasitrace, and hence no normalized quasitrace.

The CAR algebra is unital, simple, separable, nuclear, and `Z`-stable.
Therefore `psi` has exactly the domain and codomain hypotheses of Problem
LXXVIII.  But its target has finite unit, so
`stw99-lxxviii-finite-target-obstruction` proves that `psi` is not
`O_infinity`-stable.  Thus `(M_(2^infinity),C,psi)` is a counterexample to
LXXVIII.

Every step is forced by the original LXVI witness; no extra construction or
comparison assumption is introduced.
