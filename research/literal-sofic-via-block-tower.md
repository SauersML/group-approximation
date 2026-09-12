---
rg: 2
id: literal-sofic-via-block-tower
kind: route
title: Sofic core plus amenable stable letter proves the literal group sofic
target: literal-group-sofic
requires: [literal-telescope-core-lef]
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md
  - GroupApproximation/Sofic/SoficIntegerExtension.lean
---

## Why sufficient

The stable-letter exponent gives `1 -> E_T -> E -> Z -> 1`, split along
`<t>`, with `E_T = N_E semidirect T`.  `literal-telescope-core-lef` makes
`E_T` sofic, and `Z` is amenable, so `E` is sofic by the sofic-kernel /
amenable-quotient permanence of Elek--Szabo (arXiv:math/0305352), whose split
integer case is the repository's `SoficIntegerExtension.lean`.

This is the same final step as in the proof that the witness `W` is sofic
(manuscript Theorem E; `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`
(LCV12c)), and it is the VALID direction of extension permanence.  It is not
the discredited "amenable kernel with sofic quotient" direction that the
invalidated route `literal-sofic-via-amenable-kernel` used.
