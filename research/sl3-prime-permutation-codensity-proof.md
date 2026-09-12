---
rg: 2
id: sl3-prime-permutation-codensity-proof
kind: route
title: Run the established congruence co-density proof with an arbitrary inverted prime
target: sl3-prime-permutation-codensity
requires:
  - arithmetic-finite-actions-are-lambda-generated
---

The proof of `arithmetic-finite-actions-are-lambda-generated` uses no special
property of the integer `3` beyond its being the unique inverted prime.
Replace `3` by `p` throughout.  CSP puts a principal congruence subgroup of
level `m` prime to `p` in the kernel of a finite quotient.  Since `p` is
invertible modulo `m`, reduction identifies the corresponding congruence
image of `SL_3(Z[1/p])` with `SL_3(Z/m)`.  Strong approximation makes the
integral subgroup surjective onto that same image, jointly over the finitely
many levels needed for a finite action.  Hence the finite images agree.

For completeness, if `g` is outside `Lambda`, equality of all finite images
shows no finite-index subgroup containing `Lambda` can omit `g`; this is
exactly profinite density and failure of subgroup separability.  If
`Gamma/Lambda -> Gamma/H` is a finite equivariant quotient, then
`Lambda<=H`; equality of finite images forces `Gamma=H`, so the quotient is
one point.

If finite-index `H_n` converged to `Lambda` in the Chabauty topology, finite
generation of `Lambda` would give `Lambda<=H_n` eventually.  The preceding
argument would then give `H_n=Gamma`, contradicting convergence at any
element of `Gamma\Lambda`.  Thus the usual rooted-Schreier co-sofic
stabilizer criterion is unavailable as well.
