---
rg: 2
id: cyclic-coarse-fine-selector-trace-proof
kind: route
title: Sum the signed two-to-four trace deficits before taking absolute values
target: cyclic-coarse-fine-selector-rows-spread-carrier-error
requires: []
---

Put `a_i=tau(P_i)`.  The projection trace inequality gives, for every `i`,

```text
delta_i^2
 >=|tau(U_i e_i U_i^*)-tau(f_(i+1))|
 = |a_i/2-a_(i+1)/4|.                                  (CCT1)
```

Summing, using the triangle inequality, and cyclically reindexing the second
sum gives

```text
sum_i delta_i^2
 >= |sum_i (a_i/2-a_(i+1)/4)|
  = (1/4) sum_i a_i.                                   (CCT2)
```

This proves `(CCS3)` and shows explicitly why carrier masses and multiplicity
twists cannot help: only the traces of the source and target projections
enter `(CCT1)`.

For `(CCS5)`, write `p=U_i e_i U_i^*` and `q=f_(i+1)`.  Right multiplication
by the unitary reflection `U_i R_(e_i)U_i^*` gives

```text
||R_q U_i R_(e_i)U_i^*-1||_2
 =||R_q-U_iR_(e_i)U_i^*||_2
 =2||q-p||_2
 =2 delta_i.                                           (CCT3)
```

Square `(CCT3)`, sum, and apply `(CCS3)`.
