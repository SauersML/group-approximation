---
rg: 2
id: monomial-ascending-hnn-coset-action-sofic
kind: claim
title: Injective monomial polynomial self-embeddings have sofic ascending-HNN coset actions
distinct_from:
  positive-core-bernoulli-ce: That established claim concerns the positive-core Gamma-action/crossed product and already contains the local monomial stabilizer-separability trick; this claim uses all iterates of one self-embedding to prove soficity of the full ascending-HNN action, including infinite-index compressors.
  ascending-hnn-coset-action-sofic: That is the unrestricted RF/sofic-base question; this is a solved explicit family with a congruence-separability proof for every iterate.
  uas-base-gives-sofic-hnn-coset-action: That uses universal action soficity of the base; this proof needs only the concrete monomial congruence structure and applies even when that general hypothesis is unavailable.
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - docs/FALSE_POSITIVE_CORE_IS_SOFIC.md
---

Let `k=F_q`, `R=k[x_1,...,x_d]`, `r>=3`, and
`Gamma=EL_r(R)`.  Let `A in M_d(N)` have nonzero determinant and let the
monomial embedding `sigma_A:R->R` be defined by

`sigma_A(x^v)=x^(A v)`.

Let `alpha_A` be the induced injective self-embedding of `Gamma`, and let
`V_A` be its ascending HNN extension.  Then

`V_A ↷ V_A/Gamma`

is a sofic action, with no finite-index-image assumption.

For every `m`, the self-image is

`alpha_A^m(Gamma)=EL_r(k[A^m N^d])`.

The image ring is again a polynomial ring.  Suslin stability identifies the
image group with the corresponding special linear group.  If a matrix lies
outside it, some entry contains a monomial exponent outside `A^m N^d`; a
finite monomial truncation of the polynomial ring preserves that exponent and
separates the matrix from the self-image in a finite congruence quotient.
Thus every `alpha_A^m(Gamma)` is separable in `Gamma`, so every iterated base
coset action is sofic.  The established structural criterion
[[ascending-hnn-action-iff-iterated-cosets]] then gives the HNN action.

Special case: Caleb Eckhardt's compressor
`F_2[x,y] -> F_2[x,y]`, `x |-> x`, `y |-> xy`, has
`alpha^m(Gamma)=EL_3(F_2[x,x^m y])`; hence the full one-compressor HNN coset
action raised in Francesco Fournier-Facio's email is sofic.
