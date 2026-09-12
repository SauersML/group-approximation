---
rg: 2
id: finite-quotient-adjoint-wall-null-proof
kind: route
title: Average distinct kernel conjugations on normalized adjoint space
target: fixed-finite-quotient-adjoint-walls-are-canonical-trace-null
requires: []
---

Fix distinct `k_1,...,k_L in ker(q)` and put

```text
V_(i,n)=Ad(phi_n(k_i)),
A_n=(1/L)sum_i V_(i,n)
```

on the Hilbert space `M_(d_n)(C)` with normalized Hilbert--Schmidt inner
product.  The normalized Hilbert--Schmidt norm of a conjugation
superoperator satisfies

```text
(1/d_n^2) Tr_ad(Ad(U))=|tr_(d_n)(U)|^2.                 (1)
```

Therefore

```text
(1/d_n^2)||A_n||_(HS,ad)^2
 =(1/L^2)sum_(i,j)
   |tr_(d_n)(phi_n(k_i)^*phi_n(k_j))|^2.               (2)
```

Canonical moment convergence makes the diagonal terms in `(2)` equal to
one and every off-diagonal term tend to zero, because
`k_i^(-1)k_j!=1`.  Hence the right side tends to `1/L`.

If every `V_(i,n)` fixes `W_n`, then `A_n` is the identity on `W_n`.
The Hilbert--Schmidt norm of `A_n` is therefore at least
`sqrt(dim W_n)`, and `(FQW3)` follows from `(2)`.  Under `(FQW1)`, the
restriction of `A_n` to `W_n` is `o(d_n)`-close to the identity in adjoint
Hilbert--Schmidt norm, which changes the bound by `o(1)`.  First take the
microstate limit and then let `L` tend to infinity.
