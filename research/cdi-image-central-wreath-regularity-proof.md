---
rg: 2
id: cdi-image-central-wreath-regularity-proof
kind: route
title: Divide the tensor kernel by scalar cancellations and test one-site coefficients
target: cdi-image-central-wreath-retains-the-regularity-gate
requires:
  - cdi-property-t-envelope-has-nonabelian-base
  - cdi-wreath-extension-preserves-projective-basis-gate
  - cdi-standard-generator-choice-fails-projective-gate
---

Write an element of CDI's cocycle semidirect-product model as `(x,b)`.
Proposition 3.8 sends the base to

```text
gamma((pi_0(x_c))_c)=tensor_c pi_0(x_c)
```

and sends the quotient coordinate `b` to the `b`-Fourier coordinate of the
cocycle crossed product.  A nonidentity Fourier coordinate cannot equal
one.  Therefore the quotient map to `B` descends to `Lambda`, has kernel
`D`, and remains onto, proving `(CIW1)`.

If a finite tensor `tensor_c y_c`, with `y_c in Gamma`, equals one, then its
adjoint action on the `c`-th copy of the factor `M` is trivial.  Hence every
`y_c` is scalar.  The tensor itself is then `(product_c y_c)1`, so it equals
one exactly when the scalar product is one.  This proves `(CIW2)`.  A
one-site scalar tensor is the same scalar independently of its site.  After
quotienting this central subgroup `S`, the remaining base is the restricted
direct sum of copies of `Gamma/S`; conjugation permutes the copies as in the
original wreath-like extension.  This proves `(CIW3)`.

The crossed-product trace and tensor-product trace give, for finite-support
`(y_c)` and `b in B`,

```text
chi_Lambda(gamma((y_c))u_b)
 = 0                         if b != e,
 = product_c chi_Gamma(y_c)  if b = e.                 (CIW5)
```

If `chi_Gamma` is regular, then `S={1}`.  Every nonidentity base tensor has a
nonidentity coordinate, so `(CIW5)` vanishes there; it also vanishes on all
nonidentity outer Fourier coordinates.  Thus `chi_Lambda` is regular.
Conversely, restrict `chi_Lambda` to the copy of `Gamma` at one site.  This
restriction is exactly `chi_Gamma`, and the site map into `Lambda` is
injective.  Regularity of `chi_Lambda` therefore implies regularity of
`chi_Gamma`, proving `(CIW4)`.

Because `pi_tilde(G)''=N`, `chi_Lambda` is factorial.  If `N` were CE, every
tracial von Neumann subalgebra of `N`, in particular the original non-CE
algebra embedded through `M`, would be CE; hence `N` is non-CE.  The
intermediate coefficient supplied by the cited standard generator choice
survives on a one-site element by `(CIW5)`, making `chi_Lambda` nonregular.
This proves the final firewall.

Primary source: Chifan--Drimbe--Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/abs/2205.07442),
Definition 2.1, Proposition 3.8, and the proof of Theorem A(1).
