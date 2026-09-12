---
rg: 2
id: kt-internal-c-seam-kazhdan-gap-proof
kind: route
title: Apply property T to the affine permutation representation on the quotient kernel
target: kt-internal-c-seam-has-a-kazhdan-gap
requires:
  - kt-canonical-afp-seam-has-no-internal-gauge-correction
  - kun-thom-nonsofic-wreath
---

On `L^2(L(N))` define

```text
pi(gamma)(xi)=rho_gamma xi v_gamma^*.                   (KIP1)
```

This is a unitary representation of `Gamma`.  The Fourier calculation in
`kt-canonical-afp-seam-internal-no-go-proof` identifies it with the
permutation representation of the Gamma-action `(KIN4)` on `N`.  Every orbit
is infinite, so this representation has no invariant vector.  The Kazhdan
pair therefore gives

```text
max_(gamma in Q)||pi(gamma)xi-xi||_2>=kappa||xi||_2,
```

which is `(KIG1)` after multiplying on the right by `v_gamma`.

Tensoring a representation with the trivial representation on a finite
matrix Hilbert space does not create invariant vectors: it is a finite
direct sum of copies of the original representation.  The same Kazhdan
constant consequently proves the amplified assertion.  The final paragraph
of the claim is then literal bookkeeping: a flip exchanges two *different*
summand representations, while diagonal amplification repeats one.  A
covariant block induction from `<A>` to `S` has block set `S/<A>`, which is
infinite since `SL_3(Z)` is not virtually cyclic.
