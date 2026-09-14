---
rg: 2
id: hyperbolic-group-without-finite-quotients
kind: claim
title: An infinite word-hyperbolic group with no nontrivial finite quotient
distinct_from:
  rips-kernel-without-finite-quotients: that asks for a finite-quotient-free kernel of a hyperbolic Rips extension of a non-residually-finite group; this asks for a hyperbolic group that is itself finite-quotient-free
  non-residually-finite-hyperbolic-group: that asks for one invisible element; this asks for a group in which every element is invisible, and the two are equivalent only through Kapovich--Wise
  kazhdan-hyperbolic-group-without-finite-quotients: that additionally demands property (T), which is what makes the group non-MF; this is the plain Kapovich--Wise target
---

Exhibit an infinite word-hyperbolic group `G` every homomorphism of which to a
finite group is trivial.

Such a `G` is not residually finite, and conversely by
`kapovich-wise-rf-iff-finite-quotients` a non-residually-finite hyperbolic
group forces one to exist.  It is automatically non-elementary (infinite
elementary groups are virtually cyclic, hence residually finite).

## Attempts

- **Kapovich--Wise.**  `quotientless-hyperbolic-via-kapovich-wise` derives it
  from `non-residually-finite-hyperbolic-group`, so it is exactly as hard.
- **Simple hyperbolic groups.**  An infinite simple word-hyperbolic group
  would supply it.  None is known; the simple Kazhdan groups known in this
  repository (Titz--Witzel lattices, Burger--Mozes-type lattices) are CAT(0)
  lattices containing `Z^2`, hence not hyperbolic.
- **Strengthened shape.**  `kazhdan-quotientless-hyperbolic-via-common-quotient`
  shows that property (T) can always be added, and with it the group becomes
  non-MF; any direct construction may aim for that stronger shape.
