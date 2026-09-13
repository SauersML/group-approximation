---
rg: 2
id: bi-orderable-fp-n-fibre-kills-malcev-neumann-homology
kind: claim
title: If a bi-ordered group maps onto Z with kernel of type FP_n over a field, its homology with Malcev--Neumann coefficients vanishes through degree n
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
---

Let `H` be a group with a bi-invariant total order `<`, `F` a field, and
`D = F((H, <))` the Malcev--Neumann division ring of formal series with well-ordered
support. If some epimorphism `ψ: H → Z` has kernel `K` of type `FP_n(F)`, then
`H_i(H; D) = 0` for `0 ≤ i ≤ n`.

This is a Malcev--Neumann form of the vanishing half of the algebraic fibring theorems
(Kielak for the first ℓ²-Betti number of RFRS groups, Fisher for higher degrees over
arbitrary fields). It uses no Hughes-free division ring: the series supported in `K`
form a division subring `D_K`, the powers of a lift `t` of `1 ∈ Z` are linearly
independent over `D_K` because their supports lie in distinct cosets, and the
homology over the twisted Laurent ring `D_K[t^{±1}]` is `H_*(K; D_K)`, finite-dimensional
through degree `n`, hence torsion, hence killed by the Ore localization.

Proof: artifact part 1, Theorem 2.
