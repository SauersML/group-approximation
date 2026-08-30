---
rg: 2
id: folner-compression-preserves-amenable-traces-proof
kind: route
title: Compress the regular covariant representation and apply one entrywise ucp trace model
target: amenable-crossed-products-preserve-invariant-amenable-traces
requires: []
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

Write `q_r:B->A rtimes_(alpha,r) Q` for the regular quotient and represent
the reduced crossed product on the Hilbert `A`-module
`ell^2(Q) tensor A`.  For a finite Folner set `F subset Q`, compression
gives a u.c.p. map

```text
kappa_F(x)=P_F Lambda(q_r(x))P_F : B -> M_F(A).            (1)
```

Fix a finite Fourier packet `Omega`.  Let `S` contain every group
coordinate in the packet and its pairwise products.  Choose `F` with
`|partial_S F|/|F|` small.  The matrices in (1) have propagation bounded
by `S`.  Collect their finitely many entries, all entry-products used in
matrix multiplication, and all diagonal orbit coefficients.  Amenability of
`tau` supplies a u.c.p. map `phi:A->M_k` which is as
Hilbert--Schmidt-multiplicative as desired on this finite collection and whose
matrix trace approximates `tau` there.  Set

```text
Phi=(id_(M_F) tensor phi) compose kappa_F:B->M_(|F|k).      (2)
```

For `x,y in Omega` split the defect as

```text
Phi(xy)-Phi(x)Phi(y)
 =(id tensor phi)(kappa_F(xy)-kappa_F(x)kappa_F(y))
 +[(id tensor phi)(kappa_F(x)kappa_F(y))
    -(id tensor phi)(kappa_F(x))(id tensor phi)(kappa_F(y))].   (3)
```

The first term is the compressed-boundary matrix

```text
(id tensor phi)(P_F Lambda(x)(1-P_F)Lambda(y)P_F).
```

It has zero block columns away from `partial_S F`, operator norm at most
`||x||||y||`, and hence normalized Hilbert--Schmidt norm at most

```text
||x||||y|| sqrt(|partial_S F|/|F|).                         (4)
```

Entry `(i,j)` of the second term in (3) is a sum of only
`O_(Omega)(1)` defects
`phi(ab)-phi(a)phi(b)`.  Only `O_(Omega)(|F|)` block entries can be
nonzero because propagation is finite.  Therefore the normalized
Hilbert--Schmidt norm of this term is at most
`C_Omega delta`, where `delta` is the chosen entrywise defect.  First make
the Folner ratio small and then choose `phi` with `delta` small.

For a Fourier monomial `a u_g`, the matrix in (1) has zero diagonal if
`g!=e`.  If `g=e`, its diagonal consists of the finitely many orbit
coefficients `alpha_(s^-1)(a)`, `s in F`.  Thus

```text
tr(Phi(a u_g)) -> 0                         if g!=e,
tr(Phi(a))     -> |F|^-1 sum_(s in F) tau(alpha_(s^-1)(a))
                 =tau(a)                    if g=e.          (5)
```

The last equality is invariance of `tau`.  Fourier density, u.c.p.
contractivity, an exhaustion of `B`, and a diagonal choice of `F` and
`phi` give Brown's u.c.p.--Hilbert--Schmidt criterion for `sigma).

The proof only precomposes with the full-to-reduced quotient; it never asserts
that the two crossed products coincide.  The expectation and `sigma` factor
through that quotient, so this loses no trace information.
