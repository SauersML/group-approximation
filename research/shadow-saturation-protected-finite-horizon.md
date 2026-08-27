---
rg: 2
id: shadow-saturation-protected-finite-horizon
kind: claim
title: Full MF failure can be compiled beyond any prescribed finite observation horizon
distinct_from:
  full-mf-radical-finite-challenge-cylinder: that gives a clopen family of quotients of one fixed full-radical presentation; this claim approximates the shadow-bug source by varying full-radical quotients whose quotient maps preserve larger finite balls.
  common-quotient-onto-normal-subgroup: that gives protected finite-set injectivity and routing but no MF conclusion; this claim composes it with shadow saturation and records marked-group convergence.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
---

Let a finitely presented acylindrically hyperbolic group `E` contain a
nontrivial shadow bug `w` whose normal closure is suitable.  For every finite
set `F` containing `w`, there is a full-MF-radical Kazhdan AH quotient
`q_F:E->>Q_F` which is injective on `F` and routes `<<w>>` onto `Q_F`.

Taking protected balls large enough to determine each marked radius gives a
sequence of full-radical quotients converging to `E` in marked-group space.
Thus total MF failure can be placed beyond an arbitrarily large finite
observation horizon while preserving exactly the requested finite behavior.
