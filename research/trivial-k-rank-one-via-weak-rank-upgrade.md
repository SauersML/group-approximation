---
rg: 2
id: trivial-k-rank-one-via-weak-rank-upgrade
kind: route
title: Upgrade weak complexity rank one of Kirchberg algebras to complexity rank one
target: trivial-k-kirchberg-algebras-have-complexity-rank-one
requires: [kirchberg-algebras-have-weak-complexity-rank-one]
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**Dead.**  Upgrade every weak complexity-rank-one decomposition of a Kirchberg
algebra to a full one, adding the intersection algebra, and then specialize to
zero K-theory.

Invalidated by `weak-complexity-rank-one-does-not-imply-rank-one`: the upgrade
fails on Kirchberg algebras with torsion in `K_1`.  So a proof must use
`K_*(A) = 0`, or at least torsion-freeness of `K_1`, in an essential way, and
cannot be a statement about all Kirchberg algebras.
