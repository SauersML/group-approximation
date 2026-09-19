---
rg: 2
id: hs-steinberg-root-kernel-is-linear-sofic
kind: claim
title: A matricial-HS Steinberg root kernel has a linear-sofic coefficient quotient
distinct_from:
  hs-schur-toeplitz-root-defect-collapse: that asks only for the designated Toeplitz root to vanish; this is a stronger structural decoder for the whole coefficient quotient seen by all roots.
  approximate-collapse-for-kt-compressor: that asks for commutant normalization in a Laurent elementary-group compressor; this asks for a rank-metric coefficient model extracted from a tracial-HS Steinberg model.
  schur-toeplitz-root-mark-is-fd-invisible: that obtains a finite coefficient quotient from one exact finite-dimensional representation; this must replace the growing finite root kernels by one rank-ultraproduct quotient.
---

OPEN.  Let `R_f`, `H_f`, and `Gamma_f=EL_5(R_f)` be as in
`schur-toeplitz-root-mark-is-fd-invisible`, and let

```text
Phi:H_f -> U(product_omega(M_(d_n),tr_(d_n)))              (SRK1)
```

be a homomorphism.  The common root kernel

```text
K_Phi={a in R_f : Phi(x_ij(a))=1 for every i!=j}           (SRK2)
```

is a two-sided ideal: root additivity makes it an additive subgroup, Weyl
conjugacy identifies the root positions, and the Steinberg commutator formula
with two spare indices closes it under left and right multiplication.

Prove that the coefficient quotient

```text
R_f/K_Phi                                                   (SRK3)
```

is linear sofic over `k`, meaning that it embeds unitally in a rank-metric
ultraproduct of finite matrix algebras over `k` whenever it is nonzero.

This statement is exactly the missing metric conversion.  In an exact
`d`-dimensional representation, each exponent-`p` root image is finite and
`(SRK3)` is a finite ring.  In `(SRK1)`, the coordinate root spectra may grow
without bound and converge to diffuse Cantor spectra.  Hilbert--Schmidt-small
errors may also have full matrix rank, so neither finite-group exactification
nor the inequality between HS distance and rank distance supplies `(SRK3)`
for free.

The likely decoder is the finite root-character orbit.  On an exact finite
stage, conjugation

```text
x_12(a) x_23(s) x_12(a)^-1 = x_13(as)x_23(s)              (SRK4)
```

forces the spectral character set to carry the dual left-multiplication
orbit; the opposite root triangle supplies right multiplication.  The task is
to turn these finite character-orbit actions into one rank-ultraproduct
representation while retaining every coefficient outside `K_Phi`.

## Attempts

- **Direct HS-to-rank conversion fails.**  Positive HS distance of an
  exponent-`p` root from the identity does imply positive normalized rank,
  but HS-small multiplicative error need not have small rank: a full-rank
  perturbation can have arbitrarily small HS norm.  Sending the original
  coordinate matrices to a rank ultraproduct therefore does not define a
  homomorphism.
- **Finite root-table rounding is insufficient by itself.**  Any fixed
  elementary abelian root table can be exactified, with constants depending
  on that finite table.  Closing a coefficient set under arbitrary left and
  right multiplication may generate an infinite-dimensional subalgebra, so
  these separately rounded tables do not automatically assemble into a
  finite ring quotient.
- **Character-orbit attack.**  Formula `(SRK4)` and the opposite root
  triangle make the finite-stage joint spectrum carry dual left and right
  multiplication.  The promising target is a first-hit/direct-sum
  construction, analogous to Arzhantseva--Paunescu's weighted assembly of
  rank-ultraproduct morphisms, which preserves every nonkernel coefficient.
  The unresolved point is compatibility of the separately rounded spectral
  windows under multiplication.
