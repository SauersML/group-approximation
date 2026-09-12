---
rg: 2
id: exact-code-pvm-rank-transport-proof
kind: route
title: Fill the leaf-by-character integer transportation table
target: exact-code-tuples-gauge-centralize-every-pvm
requires: []
---

Put

```text
r_a=rank(f_a),       m_c=rank(p_c).
```

Both nonnegative integer families have the same total `d`.  A greedy
transportation algorithm gives nonnegative integers `n_(a,c)` with row sums
`r_a` and column sums `m_c`: repeatedly send the minimum of the first
remaining row and column mass and delete whichever is exhausted.

Inside each `f_a`, choose mutually orthogonal projections `q_(a,c)` of
ranks `n_(a,c)`.  Then

```text
q_c=sum_a q_(a,c)
```

is a PVM with `rank(q_c)=m_c=rank(p_c)`.  Two finite-dimensional PVMs with
the same labeled rank vector are simultaneously unitarily conjugate, so
there is one unitary `U` satisfying `Uq_cU*=p_c` for every `c`.  Therefore
`Uq_(a,c)U*<=p_c`, proving `(ECG1)`--`(ECG2)`.  Summing over `c` shows that
`Uf_aU*` commutes with every joint spectral projection `p_c` and hence with
every `R_i`.

