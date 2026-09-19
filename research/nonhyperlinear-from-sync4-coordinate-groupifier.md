---
rg: 2
id: nonhyperlinear-from-sync4-coordinate-groupifier
kind: route
title: Apply reverse Kleene to the fixed SYNC4 one-negative-corner groupifier
target: non-hyperlinear-group
requires:
  - fixed-sync-k-language-is-re-hard
  - sync4-coordinate-atom-normal-form
  - sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm
  - sync4-coordinate-atom-groupifier-cell
  - canonical-profile-kleene-higman
---

Apply the common-corner cell to the computable finite `SYNC_4` family.  On
HALT, its completeness clause detects the rational mark in one exact
representation.  On NONHALT, survival of the mark in a canonical-profile
matrix ultraproduct would, by `(SCG1)` and `(S4N4)`, produce a perfect CE
model of the `SYNC_4` instance, contradicting its constant gap.

These are `(CPK1)--(CPK2)` of `canonical-profile-kleene-higman`.  Reverse
Kleene and effective Higman embedding then yield a finitely presented
non-hyperlinear group.  The sole live dependency specific to this route is
`sync4-coordinate-atom-groupifier-cell`.
