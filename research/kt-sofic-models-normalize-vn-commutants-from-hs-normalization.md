---
rg: 2
id: kt-sofic-models-normalize-vn-commutants-from-hs-normalization
kind: route
title: Hilbert--Schmidt normalization specializes to permutation-valued models
target: kt-sofic-models-normalize-vn-commutants
requires: [kt-centralizer-normalization-hs]
---

An injective sofic representation `sigma : G -> S_U` with canonical trace, realized
by permutation matrices, is a trace-preserving homomorphism `G -> U(prod_U M_n)`:
the normalized trace of a permutation matrix is its fixed-point fraction, which
tends to `0` off the identity. `kt-centralizer-normalization-hs` applies to it
verbatim and gives that `sigma(G)` normalizes `sigma(Gamma)' cap prod_U M_n`.
