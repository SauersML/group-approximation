---
rg: 2
id: ce-characters-closed-multiplicative-semigroup-proof
kind: route
title: Tensor products, block direct sums, and the definition of a closure
target: ce-characters-closed-multiplicative-semigroup
requires: []
---

Direct proof, given in the claim.  Closedness is definitional (`CE` is a
pointwise closure).  The semigroup law is multiplicativity of the normalized
trace on tensor products, `tr_{de}(pi ⊗ rho) = tr_d(pi) tr_e(rho)`, plus the
observation that `conj(pi)` is again a unitary representation with
`tr(conj(pi)) = conj(tr(pi))`.  Convexity is a block direct sum with
multiplicities `round(lambda D)` and `D - round(lambda D)`, whose normalized
trace converges to `lambda tau + (1-lambda) sigma` as `D -> infinity`.
Compactness of `Ch(Gamma)` is Tychonoff on `prod_{g} {|z| <= 1}`.

No external input.
