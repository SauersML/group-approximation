---
rg: 2
id: julia-determinant-index-no-go-proof
kind: route
title: Amplify the Julia pair and perturb determinant phase at vanishing HS cost
target: determinant-index-cannot-authenticate-julia-heat-overlap
requires:
  - additive-index-instability
  - index-density-is-amplification-stable
  - julia-dilation-packages-heat-as-one-cross-gram-moment
---

Equal rank makes every ordinary square/relative index of the Julia pair
zero.  The amplification formulas from `additive-index-instability` kill
finite characters of every remaining additive defect.  The scalar sequence
`exp(i theta/d)I_d` proves directly that determinant phase has no uniform
normalized-HS modulus.

Finally the contraction ball is connected and every Julia block is unitary,
so its determinant is constant along the path from `B` to zero.  At zero the
Julia block is the coordinate swap and has determinant `(-1)^d`.  Hence the
Julia determinant contains block parity but no singular-value amplitude.
Only an extensive index density escapes these arguments, exactly as stated
in `index-density-is-amplification-stable`.
