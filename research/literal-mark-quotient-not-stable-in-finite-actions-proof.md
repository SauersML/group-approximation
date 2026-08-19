---
rg: 2
id: literal-mark-quotient-not-stable-in-finite-actions-proof
kind: route
title: Combine soficity of the marked quotient with its nontrivial finite residual
target: literal-mark-quotient-not-stable-in-finite-actions
requires: [literal-mark-quotient-sofic, literal-mark-quotient-finite-residual, sofic-stable-implies-residually-finite]
artifacts: [notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md]
---

## Why sufficient

`literal-mark-quotient-finite-residual` identifies the finite residual of
`E/<w>` as the level-collapse kernel `R` and exhibits elements of infinite
order in it, so `R != 1` and `E/<w>` is not residually finite.
`literal-mark-quotient-sofic` gives soficity.  A sofic group that is stable in
finite actions is residually finite
(`sofic-stable-implies-residually-finite`), so `E/<w>` is not stable in finite
actions; every stronger permutation stability notion implies that one, so all
of them fail.

Note the division of labour: the two soficity facts and the finite-residual
computation were produced independently — the block tower here, the
level-collapse computation by `cairn-quotient-mf` — and neither was aimed at
stability.  The stability conclusion is a corollary of putting them together.
