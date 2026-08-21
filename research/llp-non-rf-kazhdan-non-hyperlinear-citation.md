---
rg: 2
id: llp-non-rf-kazhdan-non-hyperlinear-citation
kind: route
title: LLP lifts the hyperlinear approximation to ucp maps, then the non-RF Kazhdan equivalence applies
target: llp-non-rf-kazhdan-group-is-non-hyperlinear
requires:
  - non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
---

Two inputs.

**Literature input (statement level).**  Ioana--Spaas--Wiersma,
*Cohomological obstructions to lifting properties for full C*-algebras of
property (T) groups*, GAFA 30 (2020) 1402--1438, arXiv:2006.01874,
Corollary 1.7, as quoted in Dogon arXiv:2211.10492 (v3, p. 4, the
paragraph after Theorem 1.6): "by Corollary 1.7 in [28] any group `Gamma`
such that `C^*(Gamma)` possesses Kirchberg's local lifting property (LLP)
is weakly ucp-stable."  The direct argument is sketched in the claim
(LLP lift on finite-dimensional operator systems, Arveson extension,
Stinespring dilation; the sequential form of Dogon Def 1.5 follows from
the ultrafilter form by a diagonal argument over an exhaustion of `Gamma`
by finite sets).

**Graph input.**  `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear`, direction
`(i) => (iii)`: a non-residually-finite Kazhdan group that is weakly
ucp-stable is not hyperlinear.

Composition gives the theorem.  The subgroup-permanence remark in the
claim uses only the functoriality of `(x)_max` under ucp maps and
Kirchberg's tensorial characterization of LLP (`A` has LLP iff
`A (x)_max B(l^2) = A (x)_min B(l^2)`; Kirchberg, Invent. Math. 112 (1993);
exposition in Brown--Ozawa, *C*-algebras and finite-dimensional
approximations*, Ch. 13), and is not needed for the
theorem itself.
