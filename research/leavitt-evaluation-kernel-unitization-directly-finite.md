---
rg: 2
id: leavitt-evaluation-kernel-unitization-directly-finite
kind: claim
title: The unitized kernel of the Leavitt evaluation is directly finite
refuted_by:
  - leavitt-evaluation-kernel-unitization-not-directly-finite
distinct_from:
  leavitt-evaluation-kernel-unitization-not-directly-finite: that is the invisible lifting problem; this is its negation, and each refutes the other.
  leavitt-corner-kernel-not-jacobson-radical: that refutes radical containment for the corner kernel; this asks for direct finiteness of the whole kernel's unitization, which radical containment would have given and which may still hold without it.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

**OPEN.** With `pi : F_2[R^x] ->> R` the evaluation and `K = ker pi`, the unital
subring `K^+ = F_2 1 + K` is directly finite: `(1 + v)(1 + u) = 1` with `u, v`
in `K` forces `(1 + u)(1 + v) = 1`.

This is the invisible half of `leavitt-unit-group-algebra-is-directly-finite`.
Equivalently, every direct-finiteness failure of `F_2[R^x]`, if any exists, has
a defect that survives evaluation, and so it is a lift of `(s_0, t_0)`.

## Attempts

* **Radical perturbation and separated powers.** Dead, for the reasons recorded
  in `leavitt-evaluation-kernel-unitization-not-directly-finite`: `K` contains
  proper idempotents, and infinitely many orthogonal ones.
* **Finite-dimensional representations.** Dead. They factor through the
  augmentation and kill the augmentation-zero part of `K`, where every
  invisible defect lives.
* **Proposed next attack.** Peirce analysis against the kernel idempotents. An
  invisible defect `delta` is an idempotent of `K` with `delta S (+) S ~= S`.
  Every known idempotent of `K` is supported on a finite subgroup, or is a
  `lambda`-iterate of one, and so has nonzero lifted trace
  (`finite-precision-lifted-trace-obstruction`). A defect has lifted trace zero.
  Classifying the idempotents of `K` up to equivalence, even partially, would
  bound where a defect can sit. This is not done.
* **Equivalent to the positive root (2026-09-12).**
  - By the kernel-corner transfer (`leavitt-kaplansky-failures-have-invisible-witnesses`),
    this claim is equivalent to `leavitt-unit-group-algebra-is-directly-finite`.
  - `kernel-unitization-df-from-unit-group-algebra-df` records the trivial direction.
  - The sentence above, that every failure would be a lift of `(s_0, t_0)`, is therefore
    vacuous: direct finiteness of `K^+` rules out every failure, visible ones included.
  - The proposed Peirce analysis attacks the whole Kaplansky question for `R^x`. It may
    restrict to the single corner `zSz`, `z = [1] + [g] + [g^2]`: every failure transports
    into it, with defect `delta(d) z`.
