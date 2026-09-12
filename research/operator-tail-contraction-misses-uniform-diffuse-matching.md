---
rg: 2
id: operator-tail-contraction-misses-uniform-diffuse-matching
kind: claim
title: Unique-neighbor tail contraction does not see a uniform diffuse matching profile
distinct_from:
  all-dual-unique-neighbors-contract-operator-tails: that proves the tail recurrence; this identifies its exact remaining blind regime.
  commutator-threshold-sets-need-not-be-stopping-sets: that gives a one-face threshold counterexample; this is the global small-set cutoff obstruction.
  positive-rate-tanner-tests-have-contextual-models: that constructs exact operator models; this is only a no-go for deductions from the tail recurrence and does not assert a new realizable model.
---

The recurrence `(AUT2)` cannot exclude a commutator profile which is diffuse
over all coordinates.  Indeed, take any numbers `a_L->0` and the scalar
profile

```text
q_i=a_L for every i.                                     (UDM1)
```

Then its mean square is `a_L^2->0`, but every threshold set is either empty
or all of `[L]`.  Since the all-local-dual unique-neighbor theorem applies
only when `|U_t|<=alpha L` for a fixed `alpha<1`, `(AUT2)` is vacuous on the
only nonempty tails.

This is exactly the aggregate shape of a uniformly spread high-type or
matching stress test: no coordinate is exceptional even though different
small spectral corners may carry different partners.  Therefore the
support-adaptive Loewner inequalities rule out sparse high tails and exact
sparse matching rows, but they do not rule out the diffuse matching regime.
Closing that regime still requires a common reducing cut, a range-restricted
coordinate inverse, or another mechanism coupling the moving spectral
corners.  No realizability of `(UDM1)` is claimed here.
