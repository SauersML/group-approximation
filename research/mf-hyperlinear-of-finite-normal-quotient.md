---
rg: 2
id: mf-hyperlinear-of-finite-normal-quotient
kind: claim
title: MF plus a finite normal kernel with hyperlinear quotient gives hyperlinear
distinct_from:
  mf-finite-normal-tracially-visible: That claim only makes the elements of the finite normal subgroup visible; this one assembles those with a model of the quotient to make the whole group hyperlinear.
  mf-implies-hyperlinear: This is the special case in which the failure of trace faithfulness is confined to a finite normal subgroup with hyperlinear quotient.
  finite-infranormal-subgroup-is-normal: That claim is group theory about infranormal subgroups; this one is an approximation-class transfer along a finite normal kernel.
artifacts:
  - GroupApproximation/Sofic/MFDefinitions.lean
---

Let `G` be a countable MF group with a finite normal subgroup `N` such that
`G/N` is hyperlinear.  Then `G` is hyperlinear.

This is the norm-to-trace converter of Bachner--Dogon--Lubotzky,
*On L^1-approximation of groups*, arXiv:2508.17392v3, Proposition 1.6
(verified against the source: "Let `Gamma` be a finitely generated group
with a finite normal subgroup `N` such that `Gamma/N` is hyperlinear.  If
`Gamma` is MF, then it is hyperlinear."); the route below is an independent
in-repo proof which also drops finite generation.
