---
rg: 2
id: tracial-superoperator-self-copy-proof
kind: route
title: Compare the nested conjugate zero-spectral projections in a finite tracial ultraproduct
target: tracial-superoperator-self-copy-has-no-macroscopic-excess
requires: []
artifacts:
  - notes/NONHYPERLINEAR_FINITE_MEMORY_REYNOLDS_AUDIT.md
---

Tensor telescoping gives

```text
||U tensor conjugate(U)-V tensor conjugate(V)||_2
 <=2||U-V||_2,
```

so the adjoint lifts form an exact representation `S` in the tracial
ultraproduct.  The zero-spectral projection `p_L` is the largest projection
whose range is fixed by `Q`, hence by all of `L`.  Since `H<=L`,
`p_L<=p_H`.

Exact multiplicativity gives

```text
Delta_H=S(t)Delta_LS(t)^*,
p_H=S(t)p_LS(t)^*.
```

Thus `p_L` and `p_H` have equal finite trace.  The positive projection
`p_H-p_L` has trace zero, so faithfulness gives `p_H=p_L`.

For the coordinate consequence, `e=[E_n]` is a nonzero projection dominated
by `p_H`, hence by `p_L`.  Multiplying by each `S(q)-1` and returning to
coordinates gives the asserted parent invariance.

