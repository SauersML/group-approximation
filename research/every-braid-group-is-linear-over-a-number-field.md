---
rg: 2
id: every-braid-group-is-linear-over-a-number-field
kind: claim
title: Every braid group B_n embeds in GL_m(F) for some number field F
distinct_from:
  spherical-artin-groups-are-linear-over-q-x-y: that embeds braid groups over a field of transcendence degree 2; this asks for a field algebraic over Q.
  every-braid-group-embeds-in-some-glnz: that asks for integer entries; this allows denominators, so it is weaker, and it follows from that claim.
---

For every `n` there are a number field `F`, an integer `m` and an injective
homomorphism `B_n -> GL_m(F)`.

- It follows from `every-braid-group-embeds-in-some-glnz`, via the route
  `braid-number-field-linearity-from-z-linearity`.
- It implies the non-cocompact CAT(0) reading of Problem 3.6,
  `every-braid-group-acts-properly-on-a-proper-cat0-space`, via the route
  `braid-proper-cat0-action-via-number-field-linearity`.

So it lies between the two problems. The list records the non-cocompact
question as open, which suggests this claim is open as well.

## Attempts

1. **Algebraic specialization.** It is enough to find a nonzero algebraic
   `t_0` at which the integral one-parameter representation
   `braid-groups-embed-in-gl-over-integer-laurent-polynomials` stays injective.
   Units are not needed here. The countability gap of
   `lawrence-krammer-has-a-faithful-algebraic-unit-specialization`
   (attempt 2) applies unchanged.
2. **The valuation version of Krammer's argument does not work as it stands.**
   Checked against Cohen–Wales §4, the faithfulness argument reduces modulo
   `t` and needs a cancellation-free positive cone in `R[t]/(t) = R`. With
   `t -> t_0 ∈ 𝔭` for a prime `𝔭` of `O_F`, the reduction lands in the finite
   field `O_F/𝔭`, which has no such cone. So a proof of number-field linearity
   needs a different way to rule out cancellation.
