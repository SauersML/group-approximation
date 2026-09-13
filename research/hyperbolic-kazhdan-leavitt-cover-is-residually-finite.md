---
rg: 2
id: hyperbolic-kazhdan-leavitt-cover-is-residually-finite
kind: claim
title: The hyperbolic Kazhdan cover of the binary Leavitt unit group is residually finite
distinct_from:
  leavitt-cover-regular-realizer-models-iff-residually-finite: that proves residual finiteness of this cover is equivalent to a realized sofic model with regular kernel blocks; this is the residual finiteness statement itself, recorded as the hinge of a unique-product nonsofic group.
  non-residually-finite-hyperbolic-group: that asks for some hyperbolic group that is not residually finite; the negation of this claim would give one.
---

**Statement (OPEN).**  The torsion-free word-hyperbolic Kazhdan group
`G` of `hyperbolic-kazhdan-cover-of-leavitt-unit-group` is residually finite.

**Consumers.**

- `unique-product-non-sofic-via-residually-finite-leavitt-cover`: this claim
  gives a nonsofic group with unique products.
- Its negation answers Gromov's question negatively.  The disjunction is
  `non-rf-hyperbolic-group-or-unique-product-nonsofic-group`.

## Attempts

**The standard certificate is unavailable.**  For hyperbolic groups, residual
finiteness is usually certified through a proper cocompact action on a CAT(0)
cube complex: Agol's theorem, virtual specialness, then linearity.  `G` is
Kazhdan, so it has no fixed-point-free action on a CAT(0) cube complex (Niblo--Reeves;
not re-read here).  That certificate cannot start.  `G` is built by
Belegradek--Osin small cancellation over a lattice of `Sp(2,1)` times the
Leavitt unit group, and no linear representation of `G` is known.

**What finite quotients must look like.**  Every finite image of `G` is already
the image of the kernel `N`, because the Leavitt unit group is infinite simple
(`hyperbolic-kazhdan-cover-of-leavitt-unit-group`,
`leavitt-cover-finite-quotients-split-over-the-kernel`).  Residual finiteness is
equivalent to realized sofic models with regular kernel blocks
(`leavitt-cover-regular-realizer-models-iff-residually-finite`).  No such model
is known.

**Opposing pressure.**  The relative rigid-defect statement RDD of
`nonsofic-hyperbolic-via-relative-rigid-defect` would make `G` nonsofic, hence
not residually finite.  That is the other branch of the disjunction, and it is
open too.
