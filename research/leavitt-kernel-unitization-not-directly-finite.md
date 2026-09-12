---
rg: 2
id: leavitt-kernel-unitization-not-directly-finite
kind: claim
title: Some one-sided inverse pair in F_2[R^x] lies over the identity with nonzero reverse defect
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for any strict pair; this asks for a strict pair both of whose factors evaluate to 1, the invisible half of the headline, whose defect idempotent lies in the evaluation kernel.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the visible half, with defect evaluating to s_1 t_1; this is the complementary invisible half, and the two are disjoint.
  leavitt-corner-one-sided-lift-exists: that asks for a pair in the corner eAe over the unital evaluation onto R, a visible defect; this is a kernel-local pair in the whole algebra.
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

**OPEN.** Let `A = F_2[R^x]`, `R = L_(F_2)(1,2)`, `pi : A -> R` the evaluation map and
`K = ker(pi)`. Exhibit `k, l` in `K` with

    (1 + l)(1 + k) = 1        and        (1 + k)(1 + l) != 1,

equivalently `l + k + lk = 0` and `kl != lk`.

By `leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift`, every strict pair in `A` whose
defect idempotent lies in `K` is a group translate of such a pair. So this claim together with
`left-invertible-lift-of-s0-in-leavitt-group-algebra` exhausts the headline
`leavitt-unit-group-algebra-not-directly-finite`.

## Attempts

- **Kernel corners.** If `q` in `K` is an idempotent and `qAq` has a strict pair `ba = q != ab`,
  then `1 - q + a` and `1 - q + b` witness this claim, because `a - q` and `b - q` lie in `K`.
  The kernel holds nonzero idempotents (`leavitt-corner-kernel-not-jacobson-radical`,
  `leavitt-recursive-kernel-idempotents`). Dies at the same place as every corner lane: no
  construction of a strict pair in any corner.
- **Nilpotent kernel parts.** `1 + n` with `n` in `K` nilpotent is a two-sided unit, so both
  factors need non-nilpotent kernel parts. Excluded as a mechanism, not a closure.
- **Necessary conditions** (artifact, last section): `eps(k) = eps(l) = 0`; both supports
  generate subgroups with non-directly-finite group algebras
  (`subgroup-supported-one-sided-inverse-rigidity`); the defect idempotent is not a finite sum of
  finite-subgroup projectives (`lifted-trace-detects-finite-subgroup-projectives`) and has zero
  class in `K_0(A)`. None of these gives a construction or an obstruction.
