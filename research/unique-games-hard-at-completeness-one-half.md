---
rg: 2
id: unique-games-hard-at-completeness-one-half
kind: claim
title: For every eps it is NP-hard to tell linear unique games over F_2^l of value >= (1-eps)/2 from value <= eps
distinct_from:
  unique-games-conjecture: that needs completeness 1-eps; this is the proved gap with completeness (1-eps)/2, the one-half wall.
  unique-constraints-orient-at-most-half-of-a-fiber: that explains why local unique gadgets cannot beat completeness 1/2 from 2-to-1 fibres; this is the NP-hardness statement at completeness 1/2 itself.
---

**ESTABLISHED.** For every `eps > 0` there is `l = l(eps)` such that
`Gap-UG[F_2^l]((1-eps)/2, eps)` is NP-hard. The constraints are linear,
`T x_i + T' x_j = b` with `T, T'` invertible.

**Credit.** Khot--Minzer--Safra state this consequence themselves: ECCC
TR18-006, Appendix B, p. 55, "GapUG(1/2 - eps, eps) is NP-hard". The route here
only writes out the split. Verified from the PDF on 2026-09-13; review PASS by
`ex-verify-logic-quantum`. It is not a new result.

This is the best unconditional near-0-soundness unique games hardness recorded
here. The Unique Games Conjecture asks the same with completeness `1 - eps`. The
Galois analysis (`elementary-abelian-galois-games-round-with-linear-loss`) and
the orientation barrier (`unique-constraints-orient-at-most-half-of-a-fiber`)
are two views of why the factor `1/2` is not removed locally.

DERIVATION unique-games-hard-at-completeness-one-half-proof
