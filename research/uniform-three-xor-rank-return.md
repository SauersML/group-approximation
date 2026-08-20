---
rg: 2
id: uniform-three-xor-rank-return
kind: claim
title: Return the uniform three-XOR Clifford bit at fixed scale without imposing the XOR equation
distinct_from:
  fresh-selector-renewal-after-symplectic-chart-reset: that must forget a changing nonlinear Fanizza context after an S3 chart; here every check uses one identical two-pair packet and the LCS query involutions are already globally shared.
  perfect-lcs-gap-implies-nonhyperlinear: that imposes every XOR equation as a scalar solution-group relation and therefore needs perfect completeness; this must retain failed equations as rank-jump sectors and make their multiplicity pay.
---

Given a finite three-variable LCS instance and its shared query involutions,
construct a finite group incidence that places the packet of `(TXR1)` over
every check and has the following two properties.

1. In a tracial perfect source model, all controlled packet lifts and the
   return relations have an exact realization with `J=-1`, even though the
   noisy three-XOR equations themselves are not imposed.
2. In every finite-dimensional normalized-HS microstate, total violation mass
   `q` produces an `Omega(q d)` mismatch between exact representations of one
   fixed finite packet at the return, up to `O(sqrt(E))` exactification loss.

The finite-group multiplicity theorem would then give

```text
E_return >= c q-o(1).                                    (UXR1)
```

All local packets have the same two-by-two diagonal pencil, so this target has
no predicate compiler, no changing packet size, and no tape-level selector
renewal.  The open point is a group-word return which is exact in the tracial
model but cannot discharge the extra finite-dimensional block through a
complementary representation type.  A graph of finite groups still fails by
the stationary integer-flow obstruction.

## Attempts

- A plain graph of the finite check packets fails: regular representations
  give a stationary nonnegative integer flow, so the extra rank-one branch can
  leak into complementary types instead of paying normalized-HS energy.
- Imposing each three-XOR equation as a scalar solution-group relation removes
  the violating sector rather than returning its multiplicity.  That recovers
  the perfect-completeness route and cannot use the noisy LCS gap.
- Identifying all local Clifford auxiliaries globally creates unwanted
  cross-check commutators; making them completely private loses the common
  fixed-scale packet needed at the return.
