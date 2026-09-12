---
rg: 2
id: three-shell-stabilizers-present-shell-envelope
kind: route
title: The three local presentation clauses suffice for the shell envelope presentation
target: decidable-inputs-have-fp-shell-envelopes
requires:
  - decidable-inputs-have-fp-shell-stabilizers
  - shell-cantor-embeddings-are-finite-germ-extensions
  - contracting-srn-rational-stabilizers-are-fp
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

Choose nu from the three-stabilizer hypothesis. V acts highly
transitively on Omega=V*p by finite prefix interpolation. Thus its
action on Omega^2 has finitely many orbits. For M subset F with
|F|<=2, S(M,F) is conjugate by V to A_1,A_12,A_2 when M is
nonempty. When M is empty it is the rational-point stabilizer
Fix_V(F), which is finitely presented by the required claim.
All groups required by the finite-germ theorem at n=2 are therefore
finitely presented. Applying
[Belk--Hyde--Matucci, Theorem 2.1](https://arxiv.org/html/2407.03149v1#S2.SS1)
gives E_nu finitely presented. This is only the implication from the
three-stabilizer hypothesis to the weaker envelope hypothesis.
