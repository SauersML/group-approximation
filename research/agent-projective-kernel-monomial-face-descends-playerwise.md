---
rg: 2
id: agent-projective-kernel-monomial-face-descends-playerwise
kind: route
title: Descend a two-player monomial CE face gap to one player
target: agent-projective-kernel-one-player-monomial-face-gap
requires:
  - monomial-finite-phase-ce-kernel-face-gap
  - agent-projective-kernel-factor-face-is-playerwise
---

The subgroup and character in the monomial two-player target lie in the
projective kernel of the standard factorial left-right representation.
Apply `(APF5)`.  A CE-empty face for that subgroup makes the full two-player
projective-kernel face CE-empty, and `(APF4)` then forces at least one full
one-player projective-kernel face to be CE-empty.  This is exactly the target
claim.

