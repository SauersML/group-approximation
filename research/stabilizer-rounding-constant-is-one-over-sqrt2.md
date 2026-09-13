---
rg: 2
id: stabilizer-rounding-constant-is-one-over-sqrt2
kind: claim
title: The optimal constant in stabilizer rounding of Pauli sums is 1/sqrt2
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
  - research/artifacts/pauli-stabilizer-rounding-model-test-2026-09-12.md
distinct_from:
  pauli-sums-near-their-one-norm-round-to-stabilizer-states: that proves rounding with constant 1+sqrt2; this conjectures the sharp constant 1/sqrt2, which that claim's one-qubit example shows cannot be lowered.
---

**OPEN.** For every explicit Pauli decomposition `H = sum_P beta_P P` with weight
`W = sum|beta_P|`,

```text
max_(phi stabilizer) <phi|H|phi>  >=  lambda_max(H) - (1/sqrt2)(W - lambda_max(H)).
```

The constant cannot be smaller: `(X+Z)/2` has ratio exactly `1/sqrt2`.

**Why it matters.** It would lower the NP threshold for frustration ratios from
`2+sqrt2` to `1+1/sqrt2`. That is exactly where stabilizer witnesses stop working,
by the same example. It would narrow the open window for open problem 1 of
Natarajan--Nirkhe (see `pauli-norm-games-qpcp-needs-imperfect-completeness`) to
`1 < p/q <= 1+1/sqrt2`. The multiplicative factor for Pauli-projector Hamiltonians
in `pauli-projector-hamiltonians-are-stabilizer-approximable` would become
`1+1/sqrt2`.

## Attempts

- **The averaging proof of the `1+sqrt2` bound.** It keeps signed Paulis with
  expectation above `1/sqrt2` and averages every term outside their group to zero.
  A term with expectation `e` in `(0,1/sqrt2]` then loses all of `e` while
  contributing only `1-e` to the frustration. The ratio `e/(1-e)` peaks at `1+sqrt2`.
  Reaching `1/sqrt2` needs a rounding that keeps part of those terms, for example
  by extending the commuting set greedily with sign choices. The loss analysis for
  such extensions is not done.
- **Anticommutation geometry.** Expectations of pairwise anticommuting signed
  Paulis satisfy `sum e_P^2 <= 1` (Clifford algebra), which is stronger than the
  pair bound `e_P + e_Q <= sqrt2` used in the proof. A proof might round against
  this body; no argument is written.
- **Numerical evidence.** On 7500 random instances with `n<=3` and exhaustive
  stabilizer enumeration, the largest ratio observed is `0.707107`
  (`research/artifacts/pauli-stabilizer-rounding-model-test-2026-09-12.md`). This is
  evidence, not proof; small `n` and random sampling may miss worse instances.
