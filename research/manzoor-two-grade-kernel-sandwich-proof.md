---
rg: 2
id: manzoor-two-grade-kernel-sandwich-proof
kind: route
title: Collapse each generator and compare zero grades and commuting kernel images
target: manzoor-two-grade-placement-forces-a-kernel-sandwich
requires:
  - cyclic-aperiodicity-collapses-two-actor-grade-unitaries
  - manzoor-isotropy-has-no-positive-finite-type-corner
---

By `cyclic-aperiodicity-collapses-two-actor-grade-unitaries`, for every free
generator `s` there are `B_s in U(L(A))` and `r_s in H` with

```text
Psi(pi_mu(s))=B_s U_(r_s).                             (MTP1)
```

The assignments `s |-> r_s` extend uniquely to the homomorphism `theta` in
`(MTG2)`. Multiplication in the crossed product shows that for every word
`w`, its image is homogeneous of grade `theta(w)`.

If `w notin ker(theta)`, the canonical trace kills that grade. Trace
preservation gives

```text
mu({S:w in S})=chi_mu(w)=0.                            (MTP2)
```

There are countably many such `w`, so almost surely none belongs to `S`; this
proves `S<=ker(theta)`.

If `u,v in ker(theta)`, both `Psi(pi_mu(u))` and `Psi(pi_mu(v))` lie in the
abelian base `L(A)`, hence commute. Injectivity of `Psi` gives

```text
pi_mu([u,v])=1,
```

and therefore

```text
mu({S:[u,v] in S})=chi_mu([u,v])=1.                   (MTP3)
```

Again countability permits simultaneous intersection over all pairs `u,v`,
proving `[ker(theta),ker(theta)]<=S` almost surely and completing `(MTG3)`.
---
