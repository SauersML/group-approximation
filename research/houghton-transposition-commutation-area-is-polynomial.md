---
rg: 2
id: houghton-transposition-commutation-area-is-polynomial
kind: claim
title: "In H_n (n >= 3), words centralizing the basic transposition commute with it with polynomial area"
distinct_from:
  houghton-dehn-polynomially-equivalent-to-commutation-area: that is the established reduction theorem relating the Dehn function to this area; this is the open assertion that the area is polynomial.
  houghton-groups-have-polynomial-dehn-function: that is the polynomial Dehn function statement; by the reduction theorem the two are equivalent, and this one isolates the single relation family that must be controlled.
---

For every `n >= 3` there is `k` such that for every word `z` of length `<= ℓ`
in Lee's generators with `z α z^(-1) = α` in `H_n`, `Area([z, α]) <= C ℓ^k`.
Here `α = ((1,1),(1,2))`.

## Attempts

- 2026-09-13 (z1-24-houghton): transport derivations. A shift `μ` that fixes
  `(1,1),(1,2)` commutes with `α` through a relator of bounded area, so
  `[α, D^(μ^m)]` costs `O(m)` for a deep transposition `D` given by the
  `μ`-routed word. But `μ = λ_(e,1)·ν`, with `ν` a 3-cycle on the top three
  points of ray `1`. Converting the `λ`-routed word to the `μ`-routed word
  therefore requires far commutations of `ν^(λ^i)` with the deep transposition,
  at distances up to the original one. The naive recursion
  `F(k) <= Ck + 2 Σ_(d<k) F(d) + 2P(k)` (with `F` the far-commutation areas and
  `P` the route-conversion areas) is exponential, which matches Lee's `e^x`. A
  polynomial bound needs a derivation where the conversion cost does not recurse
  at the same scale. One candidate is the exact pour identity
  `λ_(e,1) λ_(1,f) = λ_(e,f)` and its iterate
  `λ_(e,1)^m λ_(1,f)^m = λ_(e,f)^m · K'_1 ⋯ K'_m`, where each `K'_j` is a
  product of transpositions on ray `f`. This iterate is derived with `O(m^2)`
  relator applications using `[λ_(e,1), λ_(e,f)] = ((1,1),(f,1))`.
