---
rg: 2
id: idempotent-decoder-three-generators-proof
kind: route
title: Decode the idempotent by a squared commutator and extract the unit by a twisted swap
target: unit-idempotent-elementary-group-has-three-torsion-generators
requires: []
artifacts:
  - research/artifacts/pestov91-three-torsion-generators-2026-09-13.md
---

Sections 1--3 give a direct matrix proof. With `z=(ct)^4`, the decoder
identity `[z,t]^2=e_23(p)` holds in the universal idempotent coefficient
algebra. Conjugation by `z` supplies the other two directed roots with
coefficient `p`, and commutators give all six. Cancel `e_13(p)` from `t`
to recover `e_12(1-p)`; conjugation by `c,c^2` and commutators give all
complementary roots and hence the constants.

Multiply the twisted swap `w` by the recovered constant swap to get
`diag(u,u^{-1},1)`. Conjugating a constant root extracts coefficients
`u,u^{-1}`. The set of coefficients available in every root is a unital
subalgebra, so it equals `R`. All three matrices are elementary and have
the claimed orders. This proof uses no classification of finite groups.
