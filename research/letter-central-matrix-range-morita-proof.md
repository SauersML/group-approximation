---
rg: 2
id: letter-central-matrix-range-morita-proof
kind: route
title: Compress ucp maps to the stable-letter spectral blocks and take their direct sum
target: letter-central-matrix-range-separation-is-morita-neutral
requires: []
---

Let `P_j` be the spectral projection of `T` for `zeta_j`.  If
`Phi:A->M_d` is ucp, then

```text
Phi_j(a)=P_jPhi(a)P_j
```

is, after identifying `P_jM_dP_j` with `M_(d_j)`, a ucp map.  Since every
`B_s` is block diagonal,

```text
Re sum_s tr_d(B_s^*Phi(u_s))
 =sum_j alpha_j Re sum_s tr_(d_j)
                    ((B_s^(j))^*Phi_j(u_s))
 <=sum_j alpha_j h_(d_j)(B^(j)).                        (1)
```

Conversely choose ucp maps `Psi_j:A->M_(d_j)` arbitrarily close to the
individual suprema.  Their direct sum is a ucp map into `M_d`, and equality
is approached in `(1)`.  This proves `(MRS1)`.  The evaluation term against
the block-diagonal tuple `X` splits by the same normalized-trace identity,
which gives `(MRS2)`.

For the converse, the spectral blocks of `T_k` in `(MRS3)` are all copies
of `(X,B)`.  Applying `(MRS2)` gives `(MRS4)`.  Tensor amplification
preserves the normalized Hilbert--Schmidt norm and operator norm.  The
regular `k`-point spectral measure gives the stated Haar moments.

Finally

```text
W^*(T_k)=D_k tensor I_m,
T_k'     =D_k tensor M_m.
```

The trace-preserving expectation of `I_k tensor B_s` onto `W^*(T_k)` is
`tr_m(B_s)I_(km)`, so its orthogonal multiplicity component has norm
`||B_s-tr_m(B_s)I_m||_(2,m)`, independently of `k`.  This proves the last
assertion.
