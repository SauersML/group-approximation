---
rg: 2
id: finitely-generated-map-groups-are-residually-finite
kind: claim
title: A finitely generated group separated by finite-dimensional unitary representations is residually finite, so no finitely generated nonsofic group is maximally almost periodic
distinct_from:
  fournier-facio-group-finite-dimensional-shadow: that concerns the finite-dimensional shadow of one specific torsion-free nonsofic group; this is the general Mal'cev consequence for every finitely generated group, recorded because several routes tacitly use it.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

**Theorem** (classical; Mal'cev).  Let `H` be finitely generated.  If the
finite-dimensional unitary representations of `H` separate points (`H` is
maximally almost periodic), then `H` is residually finite.  Conversely
residually finite groups are MAP via their finite quotients.  Hence for
finitely generated groups, MAP is equivalent to residual finiteness.

**Consequences.**  (1) No finitely generated nonsofic group is MAP: residual
finiteness implies soficity.  So every hyperlinear model of a finitely
generated nonsofic group is genuinely asymptotic -- some `1 != w` is trivial
in every exact finite-dimensional unitary representation, yet must be
nontrivial in the normalized-Hilbert--Schmidt limit.  (2) A finitely generated
simple nonsofic group -- for instance `EL_4(L_(F_2)(1,2))`,
`binary-leavitt-elementary-group-is-simple` + `universal-leavitt-el4-nonsofic`
-- has no nontrivial finite-dimensional unitary representation at all: a
nontrivial one would be faithful by simplicity, making the group a finitely
generated linear group, residually finite by Mal'cev, hence sofic.

Recorded from the 2026-08-26 attack notebook (Section 2); the graph used
these facts tacitly in several places without a citable node.
