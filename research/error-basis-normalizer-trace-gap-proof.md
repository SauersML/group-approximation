---
rg: 2
id: error-basis-normalizer-trace-gap-proof
kind: route
title: Compute the trace of the conjugation superoperator in both bases
target: error-basis-normalizer-has-a-sharp-trace-gap
requires: []
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

Section 1 of the artifact is a complete direct proof. Orthogonality makes
the basis lines distinct, so conjugating a product two ways forces the
induced permutation `sigma` to be an automorphism of the labelling group.

Conjugation by `U` is a linear operator on the `d^2`-dimensional space
`M_d`. Diagonalizing `U` and reading it on matrix units gives trace
`sum_(i,j) lambda_i conj(lambda_j) = |Tr(U)|^2`. Reading the same
operator on the orthonormal basis `(W_a)` gives
`sum_(sigma(a)=a) xi(a)`. Equating the two is the whole computation.

A nontrivial `sigma` has fixed subgroup of index at least two, bounding
`|Tr(U)|^2` by `d^2/2`. A trivial `sigma` makes `xi` a character,
which sums to zero unless it is trivial, and a trivial `xi` makes `U`
commute with a spanning set of `M_d`, so `U` is scalar. The norm
statement follows from `||U-I||_(2,d)^2 = 2 - 2 Re tr_d(U)`.

Finiteness of the projective normalizer is the same dichotomy: the map to
`Aut(A)` has finite image, and on its kernel the character `xi`
determines `U` modulo scalars, with finitely many characters available.

Sharpness is the entrywise two-by-two computation recorded in the
artifact and rechecked there independently.
