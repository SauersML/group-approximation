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

It follows from `every-braid-group-embeds-in-some-glnz`
(route `braid-number-field-linearity-from-z-linearity`). It implies the
non-cocompact CAT(0) reading of Problem 3.6,
`every-braid-group-acts-properly-on-a-proper-cat0-space`
(route `braid-proper-cat0-action-via-number-field-linearity`). So it lies
between the two problems, and, since the non-cocompact question is recorded
as open in the list, it is presumably open too.

## Attempts

1. **Algebraic specialization of Lawrence–Krammer, units not required.** Any
   injective specialization `q -> q_0, t -> t_0` with `q_0, t_0` nonzero
   algebraic numbers gives the claim. It has the same countability gap as
   `lawrence-krammer-has-a-faithful-algebraic-unit-specialization` (attempt 2
   there), but denominators are now allowed.
2. **Idea to test: a valuation version of Krammer's argument.** Krammer orders
   the Laurent polynomials in `q` by the sign of the lowest-order coefficient,
   which makes `q` infinitesimal. Try `q -> p` (a rational prime, or a
   uniformizer of a number field) with the `p`-adic valuation playing the role
   of the lowest-order exponent, and a residue-field condition replacing the
   sign. If the cone argument survives with signs replaced by nonvanishing mod
   `p`, `B_n` is linear over `Q` or a number field, and `B_n` acts properly on a
   product of a symmetric space and Bruhat–Tits buildings. Not yet checked
   against Krammer's actual proof.
