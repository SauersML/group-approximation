---
rg: 2
id: affine-frobenius-local-storage-proof
kind: route
title: Clear rational denominators inside the full matrix Frobenius block
target: affine-frobenius-packets-solve-local-row-mask-storage
requires:
  - affine-frobenius-group-has-almost-full-simple-block
---

Dirichlet supplies primes `p=1 mod D`.  Since `D` divides `p-1`, the ranks in
`(AFP1)` are integers summing to `p-1`; choose orthogonal coordinate
projections of those ranks inside `M_(p-1)(C)`.  The block is the algebraic
corner `q_p C[H_p]q_p`, so every chosen matrix lies in the finite group
algebra.  Add a PVM on the complementary central summand `e_N` to obtain a
unital PVM.  Formula `(AFB2)` gives the exact deficit `1/p`.

For the explicit specialization, Fourier orthogonality in the cyclic
translation subgroup gives

```text
e_r^*=e_r,       e_r e_s=delta_(r,s)e_r,
sum_r e_r=1,
t e_r t^(-1)=e_(r g^(-1)).                            (1)
```

In particular `e_0=e_N` and the complement acts transitively on the
nonzero `e_r`.  If `k(r,s)` is determined by

```text
r=s g^(-k(r,s)),
```

then

```text
E_(r,s)=e_r t^(k(r,s)),             r,s!=0,            (2)
```

satisfy

```text
E_(r,s)E_(s',v)=delta_(s,s')E_(r,v),
E_(r,s)^*=E_(s,r).                                    (3)
```

This directly identifies `K[H_p]q_p` with `M_(p-1)(K)` and proves the
coefficient formulas `(AFP3)--(AFP6)`.  Since all nonzero Fourier atoms were
labelled by allowed assignments, multiplication by `q_p` annihilates the
forbidden projection.  The identity coefficient of `e_0` is `1/p`, proving
the exact mask budget.
