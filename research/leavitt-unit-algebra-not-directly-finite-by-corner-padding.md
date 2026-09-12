---
rg: 2
id: leavitt-unit-algebra-not-directly-finite-by-corner-padding
kind: route
title: Pad the corner pair with the complementary idempotent
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-corner-idempotent-unital-surjection
  - leavitt-corner-one-sided-lift-exists
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Why sufficient

Let `a, b` in `eAe` satisfy `ab = e` and `pi_e(ba) != 1_R`.  Since
`pi_e(e) = 1_R`, the inequality gives `ba != e` — this is the step the
evaluation map is for, and it is why the target claim is stated with `pi_e`
rather than with `ba != e` directly.

Set

    alpha = a + (1 - e),        beta = b + (1 - e).

Because `a = eae` and `b = ebe`, every cross term vanishes:
`a(1-e) = (ea e)(1-e) = 0` and likewise `(1-e)b = 0`, `(1-e)a = 0`,
`b(1-e) = 0`.  Hence

    alpha beta = ab + (1-e)^2 = e + (1-e) = 1,
    beta alpha = ba + (1-e),

and `beta alpha = 1` would force `ba = e`.  So `alpha beta = 1 != beta alpha`
in `A = F_2[R^x]`, which is a group algebra over a field, and Kaplansky's
Direct Finiteness Conjecture fails.

## What carries the weight

Only the corner-padding step is new here; it is elementary and unconditional,
which is precisely the point of stating the open problem in the corner.  The
whole difficulty sits in the second prerequisite.  Note also that the padding
is reversible: `A` non-directly-finite does not require the defect to come
from this corner, so the route is sufficient and not necessary.
