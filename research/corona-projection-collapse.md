---
rg: 2
id: corona-projection-collapse
kind: claim
title: Commuting-orbit projections in the corona are fixed by the compressed Kazhdan group
distinct_from:
  compression-torsion-collapse: That claim collapses group elements of finite image order; this one collapses arbitrary projections of the ambient corona algebra, group-external, by bootstrapping the involutive endpoint through a subgroup of the corona unitary group.
  commutant-projection-extraction: That claim asks for projections inside a relative commutant of a central mark; this one starts from a given projection commuting with the compressed image and concludes it commutes with the full Kazhdan image.
---

Credit: external review session (2026-08-15, unrefereed); bootstrap proof
verified in full by this session.

Let `E` be countable, `L <= E` with property (T), `s L s^{-1} <= L`, and
let `pi : E -> U(Q)` be any norm-matrix-corona representation.  Let
`p in Q` be a projection with

1. `[p, pi(s L s^{-1})] = 0`;
2. the projections `pi(gamma) p pi(gamma)^*`, `gamma in L`, commute
   pairwise.

Then `[p, pi(L)] = 0`.

**Scope.**  The witness is no longer a group element: it is an arbitrary
projection of the corona.  Consequently every unital projection-generated
C-star subalgebra `B <= Q` whose elements centralize the compressed image
and whose projection orbits commute satisfies `B <= pi(L)'` — finite
spectral packets, AF packets, and arbitrary zero-dimensional commutative
packets at once.  The dividing line of the collapse phenomenon is not
involution-versus-torsion but projection-generated spectral data versus
connected spectral data (`spectral-component-motion-bound`,
`corona-commutant-growth-witness`).
