---
rg: 2
id: agent-projective-kernel-one-player-route-to-nonhyperlinear
kind: route
title: Compile a one-player monomial projective-kernel CE gap into a nonhyperlinear group
target: non-hyperlinear-group
requires:
  - agent-projective-kernel-one-player-monomial-face-gap
  - agent-projective-kernel-arbitrary-phase-face-compiler
---

Choose the player whose full projective-kernel face is CE-empty.  Its
question group is a finite free product of finite cyclic groups and hence is
finitely presented.  Apply the arbitrary-phase face compiler to this player
group, its full projective kernel, and its scalar character.  The output is a
finitely presented nonhyperlinear central extension.

