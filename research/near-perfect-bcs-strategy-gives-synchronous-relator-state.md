---
rg: 2
id: near-perfect-bcs-strategy-gives-synchronous-relator-state
kind: claim
title: A near-perfect BCS strategy gives a synchronous approximate relator state with an explicit modulus
artifacts:
  - research/artifacts/fanizza-npa-ingestion-delta-2026-08-20.md
distinct_from:
  fanizza-et-al-computable-bcs-signal-family: that supplies a special machine family and its final distinguished-signal estimate; this is the general strategy-to-state interface for any finite BCS.
  msz-polynomial-doubling-survives-synchronous-states: that propagates a particular additive recurrence once synchrony and relator control are available; this produces precisely those hypotheses from a near-perfect game strategy.
---

Let `B` be a finite BCS with `k` constraints and maximum context size `M`,
and put

```text
T_B=4^(M+2) k M^3.                                               (NPS1)
```

For every `epsilon`-perfect commuting-operator strategy `S` for the
constraint-variable BCS game, its associated Bob state `phi_S` has an
extension `f` to the tensor square of the free involution algebra such that

```text
f o iota = phi_S,
f is (T_B epsilon,X)-synchronous,                                (NPS2)
phi_S is a (T_B epsilon,R(B))-state.                             (NPS3)
```

Thus game loss simultaneously controls Alice--Bob generator disagreement,
the commutator relations inside every context, and the forbidden-assignment
projection.  The constant is computable from the finite BCS alone and is
valid for arbitrary commuting-operator strategies, not only
finite-dimensional ones.
