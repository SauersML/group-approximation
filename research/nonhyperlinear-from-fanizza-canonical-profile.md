---
rg: 2
id: nonhyperlinear-from-fanizza-canonical-profile
kind: route
title: Apply the canonical-profile reverse-Kleene compiler to the Fanizza native mark
target: non-hyperlinear-group
requires:
  - fanizza-canonical-profile-groupification
  - canonical-profile-kleene-higman
---

The two clauses of `fanizza-canonical-profile-groupification` are exactly
`(CPK1)--(CPK2)`. Apply `canonical-profile-kleene-higman` to obtain a
finitely generated recursively presented non-hyperlinear group, then its
effective finitely presented Higman overgroup.
