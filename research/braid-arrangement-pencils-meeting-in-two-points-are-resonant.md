---
rg: 2
id: braid-arrangement-pencils-meeting-in-two-points-are-resonant
kind: claim
title: "Two pencil planes of the braid arrangement whose puncture sets meet in exactly two points span a degree-2 resonant subspace"
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-pencils-2026-09-13.md
---

Let `n >= 5` and let `U_1, U_2 <= [n+1]` be 4-element sets with `|U_1 ∩ U_2| = 2`.
In the symmetric coordinates of `pure-braid-sunflower-characters-obstruct-bnsr-invariants`,
the 4-dimensional subspace `L_{U_1} + L_{U_2} <= H^1(P_n; C)` lies in the
degree-2 resonance variety `R^2(P_n)` of the braid arrangement.

## Attempts

- Explicit cocycle: for `a = b_1 + b_2` (`b_i in L_{U_i}`) and `b_i^⊥ in L_{U_i}`
  independent of `b_i`, `a ∧ b_1^⊥ ∧ b_2^⊥ = 0`, because components of `R^1` are
  isotropic. Resonance holds iff `b_1^⊥ ∧ b_2^⊥` is not in `a ∧ A^1`.
- Evidence, not proof: for `n = 5`, all 45 such pairs give `dim H^2 = 1` at a
  random point, computed mod `2^31 - 1` (artifact Section 3). These 45
  subspaces are not inside any 5-point pullback, so the six-subspace
  prediction for `R^2(P_5)` was incomplete.
- Reduction to `n = 5`: forgetful maps split, and the Aomoto complex of the
  quotient is a retract, so resonance at `n = 5` pulls back to every `n`.
- Missing: an exact certificate, e.g. a linear functional that vanishes on
  `a ∧ A^1` for all parameters and not on `b_1^⊥ ∧ b_2^⊥`, or a symbolic rank
  computation over `Q(parameters)`.
