---
rg: 2
id: braid-groups-embed-in-gl-over-integer-laurent-polynomials
kind: claim
title: Every braid group B_n embeds in GL_M(Z[t, t^-1]) with M = n(n-1)
distinct_from:
  spherical-artin-groups-are-linear-over-q-x-y: that places spherical Artin groups over the field Q(x,y), with two transcendental parameters; this uses one formal parameter over the integers, so the only step left for Problem 3.2 is a faithful value of that parameter.
  every-braid-group-embeds-in-some-glnz: that asks for integer matrices; this allows entries in the Laurent polynomial ring Z[t, t^-1], a ring of Krull dimension 2 that is not finitely generated as an abelian group.
---

For every `n >= 2` there is an injective homomorphism
`B_n -> GL_(n(n-1))(Z[t, t^{-1}])`. The same holds, with `M = 2|Φ^+|`, for
every Artin group of type `A`, `D` or `E`.

So Problem 3.2 (`zaremsky-3-02-braid-groups-embed-in-glnz`) comes down to
removing a single formal parameter from a faithful representation with
integer coefficients.

Proof: `braid-groups-embed-in-gl-over-integer-laurent-polynomials-proof`.
