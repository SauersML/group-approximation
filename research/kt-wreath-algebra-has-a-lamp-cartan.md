---
rg: 2
id: kt-wreath-algebra-has-a-lamp-cartan
kind: claim
title: For q=2 the Kun--Thom wreath algebra is a II1 factor with the lamp algebra as a Cartan masa
distinct_from:
  coset-wreath-algebra-has-a-lamp-cartan: that is the same Cartan package for the ARITHMETIC summit wreath W_3, which is not known to be nonsofic; this is for the Kun--Thom wreath, which is nonsofic by Kun--Thom Theorem A, over a pair whose freeness has a different proof.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  Let `W = (direct_sum_(G/Gamma) Z/2Z) rtimes G` be the
Kun--Thom wreath for the Theorem E pair with `q = 2` (more generally any `q`
with `gcd(r,q-1) = 1`).  Put `X = {-1,1}^(G/Gamma)` with Bernoulli(1/2)
measure.  Then

1. `L(W) = L^infinity(X) rtimes G`, the lamp group algebra being
   `L^infinity(X)` through Fourier--Walsh duality;
2. `L(W)` is a II_1 factor;
3. `A = L^infinity(X)` is a Cartan subalgebra of `L(W)`: diffuse, hyperfinite,
   maximal abelian and regular.

For general `q`, the finite central kernel `Z_q` of
`kt-coset-bernoulli-essentially-free` is central in `W`, so `L(W)` splits over
the characters of `Z_q` into `gcd(r,q-1)` twisted crossed products of the free
ergodic action of `G/Z_q`, each carrying the same lamp Cartan.

DERIVATION
kt-wreath-lamp-cartan-proof
