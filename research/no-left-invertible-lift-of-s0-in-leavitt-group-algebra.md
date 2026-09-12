---
rg: 2
id: no-left-invertible-lift-of-s0-in-leavitt-group-algebra
kind: claim
title: No lift of s_0 to the Leavitt unit group algebra is left invertible
refuted_by:
  - left-invertible-lift-of-s0-in-leavitt-group-algebra
distinct_from:
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the visible lifting problem asking for a left-invertible lift; this is its negation, and each refutes the other.
  leavitt-rank-three-lift-has-no-one-sided-inverse: that excludes one explicit support-three lift through its virtually free support group; this excludes every lift of s_0.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

**OPEN.** For every `a` in `F_2[R^x]` with `pi(a) = s_0` and every `b`,
`b a != 1`.

This is the visible half of `leavitt-unit-group-algebra-is-directly-finite`. By
`leavitt-inverse-defects-are-visible-or-invisible` it is equivalent to: every
direct-finiteness failure of `F_2[R^x]`, if any exists, has a defect killed by
evaluation. It also closes the one linear architecture that reads
`leavitt-kernel-annihilator-strict-self-embedding` as a full-shift automaton.

## Attempts

* **Location rigidity.** Partial. By
  `subgroup-supported-one-sided-inverse-rigidity`, a left-invertible lift must
  have support generating a subgroup whose group algebra is not directly finite.
  That kills the explicit support-three lift
  (`leavitt-rank-three-lift-has-no-one-sided-inverse`), but it cannot reach lifts
  whose support generates a nonsofic subgroup, and every generating set of
  `R^x` is such a support.
* **Augmentation.** A left-invertible lift has `eps(a) = 1`. Parity is repairable
  by kernel elements of augmentation one
  (`leavitt-evaluation-kernel-hits-augmentation-one`), so this is no obstruction.
* **Completing the family.** A witness can never be completed to a lift of all
  four Leavitt generators, by the augmentation argument (Proposition 6 of the
  artifact). This restricts the witness's shape but does not exclude it.
