---
rg: 2
id: tail-tensor-representations-realize-kazhdan-staircases
kind: route
title: Use distinct prime quotient factors to realize every staircase level as an irreducible tail
target: kazhdan-staircase-heats-defeat-rank-height-bounds
requires: []
artifacts:
  - research/artifacts/kazhdan-staircase-heat-and-central-height-2026-09-08.md
---

For distinct primes `p_1,...,p_n`, let `sigma_l` be the projective-point
augmentation representation of `SL_3(F_(p_l))`, of degree
`r_l=p_l^2+p_l`. Two-transitivity proves irreducibility. The Chinese
remainder theorem makes reduction of `SL_3(Z)` onto the product
surjective, so the tail tensors `rho_j=sigma_(j+1) tensor ... tensor
sigma_n` are irreducible and pairwise inequivalent. With
`a_j=product_(l<=j) r_l` and `D=product_l r_l`, the representation
`direct_sum_(0<=j<n) I_(a_j) tensor rho_j` has equal physical blocks
of size `D` and commutant `direct_sum_j M_(a_j) tensor I_(D/a_j)`.

The common last factor proves canonical character convergence when
`p_n->infinity`: every fixed nonidentity integer matrix is eventually
non-scalar modulo `p_n`, and its normalized projective augmentation
character has absolute value at most `1/p_n`.

Cyclically shift the equal physical blocks in the direction making
each interior algebra grow by the next tensor factor. Forward failure
is confined to the last block of trace `1/n`; a traceless unitary in
the newly added factor attains reverse failure on all other blocks.
Linear central heights have the displayed variance and shift error.
Their strictly separated log weights also imply that a central corner
with fixed bounded trace distortion contains only boundedly many levels.

The positive Kazhdan constant for the fixed elementary generators of
`SL_3(Z)`, supplied by
[Kassabov's Theorem A](https://arxiv.org/abs/math/0311487v1), gives a
uniform gap for the exact adjoint representations. Laziness puts their
spectra in `[0,1-gamma] union {1}`. Powers have at most `13^k` Kraus
operators and approximate the actual commutant expectations uniformly.
Comparison with continuous heat proves the fixed-tolerance rank bound.
All representation, character, norm and weight calculations are given
in the artifact; no native Leavitt realization is used or asserted.
