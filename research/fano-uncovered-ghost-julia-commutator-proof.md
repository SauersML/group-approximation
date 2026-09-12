---
rg: 2
id: fano-uncovered-ghost-julia-commutator-proof
kind: route
title: Package the weighted ghost row in its Julia reflection
target: fano-uncovered-ghost-energy-is-one-julia-commutator
requires: []
---

Since `P_c` and `F_c` commute, `Q_c=(1-P_c)F_c` is a projection.  For the
row operator `T xi=(sqrt(mu_c)Q_cS xi)_c`,

```text
T^*T=S^*(sum_c mu_c Q_c)S<=S^*S<=1,
```

so `T` is a contraction, and normalized trace gives exactly
`tau_H(T^*T)=L_forb`.

The defect-operator identity `T D_T=D_(T^*)T` makes the standard Julia
matrix `j_T` a self-adjoint unitary.  With grading
`z=diag(1_H,-1_(direct-sum_c H))`, direct block multiplication gives

```text
zj_Tz-j_T=[[0,-2T^*],[-2T,0]].
```

Right multiplication by `j_T` is unitary, hence the unnormalized squared
Hilbert--Schmidt norm of `zj_Tzj_T-1` is `8 Tr_H(T^*T)`.  Division by the
ambient dimension `(m+1)dim(H)` proves

```text
||zj_Tzj_T-1||_2^2=8 L_forb/(m+1).
```

If `L_forb=0`, faithfulness of finite-dimensional trace gives `T=0`, so
`j_T=z` and the word is exactly one.  This is only the asserted
state-dependent operator reduction; authentication by fixed group syntax
remains a separate problem.
