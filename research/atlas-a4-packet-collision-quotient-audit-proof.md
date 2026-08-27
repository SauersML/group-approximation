---
rg: 2
id: atlas-a4-packet-collision-quotient-audit-proof
kind: route
title: Proof of the finite stability-or-countermodel fork for the A4 packet-collision quotient
target: atlas-a4-packet-collision-quotient-audit
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-two-context-collision-gap
---

Let `i_1,i_2:A8 -> Q_A4` be the two factor maps.  Simplicity of `A8` makes
each kernel either trivial or all of `A8`, proving the first assertion.

Assume `Q_A4` is finite.  Every relation in its complete multiplication table
has some finite van Kampen area over the emitted finite presentation.  Taking
the maximum over the finite table converts sufficiently small presentation
defect into an all-pairs approximate representation of `Q_A4`.  Flexible
Hilbert--Schmidt stability of finite groups then perturbs it, after the usual
bounded relative dimension change, to an exact representation of `Q_A4`.

If (say) `i_1` is trivial, every exact representation kills the first `A8`
factor.  It cannot be close to a regular amplification of that factor: for any
nonidentity `g in A8`, the exact image has normalized trace one while the
regular image has normalized trace zero.  The trace difference is bounded by
normalized HS distance.  Hence the assumed exact-regular necessity sequence
cannot exist.

If both factor maps are injective, restrict the left regular representation of
`Q_A4` to either subgroup.  The subgroup acts freely on every left coset, so
the restriction is exactly `[Q_A4:A8]` copies of `Reg(A8)`.  All thirty packet
words and `q_19243` vanish by definition.  Were the two subgroups the same up
to an automorphism, that automorphism would be one of the inner/outer `A8`
alignments exhausted by the classical packet audit, contradicting the zero
packet-plus-collision survivor count.  This proves the countermodel branch.
