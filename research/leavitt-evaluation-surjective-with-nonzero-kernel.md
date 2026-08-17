---
rg: 2
id: leavitt-evaluation-surjective-with-nonzero-kernel
kind: claim
title: Evaluation from the group algebra onto the Leavitt algebra is onto with nonzero kernel
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that is the internal structure of the unit group, identifying `GL` with `EL` and proving perfectness; this is about the map from the group algebra of that unit group back onto the ring, and about what its kernel contains
  augmentation-blocks-unital-leavitt-family: that says a group ring never *contains* a binary Leavitt family; this says a group algebra always *surjects onto* one when the group is the unit group, which is the opposite direction and is compatible with it
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
  - GroupApproximation/Leavitt/Leavitt.lean
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`, and let

    pi : S -> R,      pi(sum c_g [g]) = sum c_g g

be the canonical unital ring homomorphism.  Then:

1. `pi` is **surjective**;
2. `K = ker(pi)` is **nonzero**;
3. `K` is **not** contained in the augmentation ideal: some `k` in `K` has
   `eps(k) = 1`.

Part 1 is the unit-span theorem
(`unitAdditiveSpan_eq_top`, `UnitAdditiveSpan.lean`, kernel-checked) plus
characteristic two.  Parts 2 and 3 both come from the fact that `R` admits no
unital ring homomorphism to `F_2`.

## What each part is for

Part 1 is what makes `R^x` a candidate at all: the group algebra of the unit
group sees the whole ring, so ring-level phenomena are in principle
expressible over the group.

Part 2 is what makes the annihilator subshift of
`leavitt-kernel-annihilator-strict-self-embedding` **proper** — and hence
also what stops it from being a Gottschalk counterexample.

Part 3 is a small but load-bearing negative result: the parity of a lift is
not an invariant, so the augmentation obstruction that kills the natural
four-unit lift of `s_0` is repairable and does not obstruct
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.
