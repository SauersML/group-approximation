---
rg: 2
id: finite-pauli-seed-quarter-carrier-proof
kind: route
title: Exactify D8, average the context, and use the Pauli trace flip
target: finite-pauli-seed-reducing-quarter-carrier
requires: []
---

Spectral sign rounding first makes `J` an involution. Averaging `B,C` over
`J` and applying functional calculus makes them commuting with `J`; another
fixed correction makes them involutions. On the `J=1` sector, average `C`
over the exact `B` action and apply functional calculus once more, producing
exact commuting involutions. On the `J=-1` sector, block `C` relative to the
two `B` eigenspaces. Unitarity gives

```text
|r_+-r_-|/d <= (1/4)||BC+CB||_(2,d)^2.
```

Thus only `O(E)` normalized dimension is unmatched; reassign it and replace
`C` on the matched part by the exact off-diagonal involution obtained from the
polar part of its off-diagonal block. The diagonal-block defect and unitarity
control this polar correction in normalized-HS norm. This exactifies the
fixed `D_8` seed at `O(sqrt(E))` cost.

Average every contextual generator over the resulting eight-element action.
The eight-term conditional expectation is within `O(sqrt(E))` by the supplied
commutator relators. Functional calculus and the assumed structural rounding
then run blockwise inside the seed commutant, with dimension-independent
constants after normalized-trace weighting. This proves the reducing claim.

On `Q_-`, the exact relation is `CBC=-B`; hence `C` bijects the two `B`
eigenspaces and proves `(PSQ3)`. Tensoring the perfect contextual model with
the Pauli matrices proves exact consistency and nontriviality of `J`.
Canonical trace separation then gives `(PSQ4)`.
