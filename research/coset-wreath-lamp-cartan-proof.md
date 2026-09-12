---
rg: 2
id: coset-wreath-lamp-cartan-proof
kind: route
title: Freeness plus Fourier-Walsh ergodicity make the lamp algebra Cartan
target: coset-wreath-algebra-has-a-lamp-cartan
requires:
  - coset-bernoulli-action-is-essentially-free
---

`L(direct_sum_I C_2) = L^infinity({-1,1}^I)` equivariantly by Fourier
transform, carrying the counting trace to Bernoulli(1/2); hence
`L(W_3) = L^infinity(X) rtimes Gamma` with the canonical trace.
Ergodicity: `L^2(X)` has the Walsh basis `w_F` indexed by finite
`F subset I`, permuted by `Gamma`; a setwise stabilizer of a nonempty
finite `F` meets a point stabilizer `x Lambda x^{-1}` in finite index,
and `[Gamma : x Lambda x^{-1}]` is infinite, so all nonempty-`F` orbits
are infinite and an invariant `ell^2` coefficient function vanishes off
the vacuum.  Essential freeness (the prerequisite) gives maximal
abelianness of `L^infinity(X)` in the crossed product; the group
unitaries normalize it, so it is regular; free + ergodic + p.m.p. give
a II_1 factor.  These conversions are the standard Feldman–Moore /
Murray–von Neumann facts for free ergodic probability-preserving
actions.  Full text: artifact
`research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md`,
Theorem 2.
