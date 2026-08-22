---
rg: 2
id: sl3-double-quasiregular-tensor-outlier-proof
kind: route
title: Correcting the tensor would turn its quasi-regular base vector into an ambient fixed vector
target: sl3-double-quasiregular-tensor-is-a-uniform-outlier
requires:
  - sl3-double-tensor-leak-is-quasiregular
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Let `Omega_n` be the normalized maximally entangled vector.  The first
prerequisite gives

```text
<rho_n(a)Omega_n,Omega_n> -> 1_C(a).                           (QTP1)
```

Suppose, contrary to `(QTO2)`, that exact representations
`alpha_n:A->U(d_n^2)` approach `rho_n` on `S_A`.  Fixed-word telescoping and
`(QTP1)` show that `Omega_n` is asymptotically invariant under a fixed
Kazhdan set of `alpha_n(C)`.  Property (T) of `C` therefore gives unit
vectors `eta_n` with

```text
||eta_n-Omega_n|| -> 0,       alpha_n(c)eta_n=eta_n (c in C). (QTP2)
```

Finite-dimensional co-density upgrades `C`-fixed vectors to `A`-fixed
vectors.  To see this directly from the commutant form already imported in
`exact-projective-codensity-has-a-uniform-trace-square-gap`, apply it to
`1 direct_sum alpha_n`.  The off-diagonal operator determined by `eta_n`
intertwines the trivial representation with `alpha_n|_C`; equality of the
`C`- and `A`-commutants says it also intertwines `A`.  Hence

```text
alpha_n(a)eta_n=eta_n       for every a in A.                  (QTP3)
```

Choose `h=diag(2,1,1/2) notin C`.  Closeness of `rho_n(h)` to
`alpha_n(h)`, together with `(QTP2)--(QTP3)`, makes the left side of `(QTP1)`
at `h` tend to one.  But `(QTP1)` says it tends to zero.  This contradiction
proves a positive uniform lower bound by the usual subsequence argument.

For a fixed tensor power, use `Omega_n` to the same tensor power.  Its
coefficient is `1_C(a)^k=1_C(a)`, so the proof is unchanged.

