---
rg: 2
id: linear-decoders-with-coboundary-functionals-admit-no-section
kind: claim
title: A linear decoder with a uniform output functional pulling back to a coboundary along one element, or with finite nonzero kernel, has no measurable section
distinct_from:
  ornstein-weiss-type-decoders-admit-no-measurable-section: that treats one two-term difference row with arbitrary maps of symbols; this treats linear decoders through any finitely supported output functional, including annihilators and finite kernels.
  homomorphic-codes-cannot-compress-bernoulli-shifts: that kills linear encoders; this kills linear decoders of arbitrary Borel encoders.
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
---

Let `G` be countable, `F = F_p`, and let `L(y)(g) = sum_s y(gs) R_s` be a linear decoder
`(F^m)^G -> (F^(m'))^G`, with adjoint `(R*q)(h) = sum_s R_s q(h s^-1)` on finitely supported `q`. There is no
Borel equivariant `tau` with `L o tau = id` almost everywhere if either

1. `R*q = v - a.v` for some `a` in `G` and finitely supported `q, v`, where `q` has a nonzero sum over some right
   coset of `<a>` (or `sum_(k<N) a^k.q != 0` when `a` has finite order `N`); or
2. `ker L` is finite and nonzero.

**Special cases.**
- The annihilator case `R*q = 0` with `q != 0`.
- The linear two-term rows of `ornstein-weiss-type-decoders-admit-no-measurable-section`.

**Proof idea.**
- For item 1, `Q(x) = <tau(x), v>` satisfies `Q(x) - Q(a^-1.x) = <x, q>`. Modulo cylinder coboundaries, `<x, q>`
  has one coordinate per coset of `<a>`, and partial sums conjugate the skew product to a Bernoulli shift, so no
  such `Q` exists.
- For item 2, the image of a section and its kernel translates split a conull set into finitely many invariant
  pieces of equal measure.

A section with `ker L = 0` forces a stable finiteness failure `SR = I_(m')` over `F_p[G]`.

Proof: Section 5 of the artifact, route `linear-decoder-coboundary-functionals-proof`.

**ESTABLISHED 2026-09-12** by [[linear-decoder-coboundary-functionals-proof]]. Verification requested from
w3-vf-nonlinear.
