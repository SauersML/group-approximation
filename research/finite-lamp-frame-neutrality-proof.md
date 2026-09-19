---
rg: 2
id: finite-lamp-frame-neutrality-proof
kind: route
title: Separate a finite conjugate-lamp window in a finite regular quotient
target: finite-lamp-frame-is-matrix-range-neutral
requires: []
---

Put

```text
K_(k,q)=<a,h_1,...,h_q | a^k=1>=C_k * F_q,
z_0=a,                  z_i=h_i a h_i^(-1).                       (1)
```

The Bass--Serre normal form (equivalently, Kurosh's subgroup theorem)
identifies

```text
<z_0,...,z_q> = *_(i=0)^q <z_i> = *_(i=0)^q C_k.                 (2)
```

The virtually free group `K_(k,q)` is residually finite.  Given `Omega`,
choose one finite quotient `r:K_(k,q)->Q` which retains every word in
`Omega` and every `a^j`, `1<=j<k`.  In the left regular representation of
`Q`, set

```text
T=lambda(r(a)),          H_i=lambda(r(h_i)),
T_i=lambda(r(z_i)).                                             (3)
```

Every retained nonidentity word has trace zero.  Since `r(a)` has exact
order `k`, every conjugate `T_i` has uniform `k`-point spectrum.  This
proves the finite-frame assertions.

Tensor `(3)` by `I_m`.  For every ucp map
`Phi:A->M_|Q| tensor M_m`, its partial trace

```text
Psi=(tr_|Q| tensor id) circle Phi:A->M_m
```

is ucp and gives

```text
 Re sum_s tr((I tensor B_s)^* Phi(u_s))
 =Re sum_s tr_m(B_s^*Psi(u_s))
 <=h_m(B).                                                       (4)
```

Conversely `Phi(a)=I tensor Psi(a)` attains the reverse inequality up to
the same optimization error.  Hence the support functions agree.  The
evaluation on `I tensor X` and all normalized Hilbert--Schmidt/operator
norms are unchanged, proving `(FLF3)`.
