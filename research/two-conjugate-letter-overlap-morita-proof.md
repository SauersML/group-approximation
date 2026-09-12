---
rg: 2
id: two-conjugate-letter-overlap-morita-proof
kind: route
title: Approximate the conjugate cyclic letters by finite regular quotients and tensor the separator
target: two-conjugate-letter-overlap-data-is-morita-neutral
requires: []
---

Fix `k` and put

```text
F_k=<a,h | a^k=1> = C_k * Z,          b=hah^(-1).
```

By the normal-form theorem the subgroup `<a,b>` is `C_k*C_k`.  The group
`F_k` is residually finite.  Given a finite window `Omega` of nonidentity
words in `<a,b>`, choose a finite quotient `q:F_k->Q` which keeps every
word of `Omega` nontrivial and keeps `a^j` nontrivial for `1<=j<k`.
In the left regular representation of `Q`, set

```text
T_k=lambda(q(a)),        H_k=lambda(q(h)),
U_k=H_kT_kH_k^*=lambda(q(b)).                            (1)
```

Regular traces vanish on all retained nonidentity words.  The order of
`q(a)` is exactly `k`; hence `T_k,U_k` have uniform `k`-point spectra.
Taking windows increasing to all words and `k->infinity` recovers the
canonical free-Haar joint moments of the two conjugate HNN letters.

Let `r=|Q|` and tensor `(1)` with `I_m`.  Put
`X~_s=I_r tensor X_s` and `B~_s=I_r tensor B_s`.  These tuples commute with
both letters.  For every ucp map `Phi:A->M_r tensor M_m`, the partial trace

```text
Psi=(tr_r tensor id) circle Phi:A->M_m
```

is ucp, and

```text
Re sum_s tr_(rm)((I_r tensor B_s)^*Phi(u_s))
 =Re sum_s tr_m(B_s^*Psi(u_s))
 <=h_m(B).                                                (2)
```

Conversely `Phi(a)=I_r tensor Psi(a)` for an almost optimizing `Psi` shows
equality in `(2)`.  The evaluation against `X~` also equals the original
evaluation against `X`, proving `(TLM2)`.  Tensoring preserves normalized
Hilbert--Schmidt norms and operator norms.

Finally place any finite-dimensional representation of the common overlap
group `C` on `C^m`.  It commutes with both letters.  Whenever its trace is
canonical on a prescribed finite `C`-window, the product trace is canonical
on the corresponding retained window in
`C direct_product <a,b>`.  Residual finiteness of the arithmetic overlap
supplies such finite-window actor models.  This proves all assertions.
