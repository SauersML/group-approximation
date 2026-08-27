---
rg: 2
id: mf-compiler-positive-branch-torsion-free-proof
kind: route
title: Torsion in an amalgam or an HNN extension is conjugate into a vertex group
target: mf-compiler-positive-branch-is-torsion-free
requires:
  - mf-safe-finite-presentation-compiler
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

Direct proof in the claim body: every building block of the positive
branch is a free group, a finite direct product of free groups, a
subgroup of such, an amalgam over a common subgroup, or an HNN extension
of a torsion-free base, and each of these operations preserves
torsion-freeness (for amalgams and HNN extensions because torsion is
conjugate into a vertex group).
