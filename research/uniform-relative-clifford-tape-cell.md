---
rg: 2
id: uniform-relative-clifford-tape-cell
kind: claim
title: Each new Clifford tape cell exactifies relative to the old prefix with a rank-independent constant
distinct_from:
  quantum-expander-rounds-relative-pauli-cell: that is an abstract matrix lemma assuming expander unitaries are already available; this supplies them as level-indexed words of one finite presentation.
  finite-dimensional-schur-lift-of-doubling-tape: that still must compose the cells and charge inactive selector sectors; this is only the uniform one-step relative exactification.
---

For one finitely presented Clifford tape, every level `n` has the following
uniform property. Conditional on an exactified old prefix `E_n`, a proposed
new controlled Pauli cell whose finite template relators have defect `delta`
can be flexibly exactified relative to `E_n` with normalized-HS loss
`O(delta)` and discarded density `O(delta^2)`, where the constants are
independent of `n`.

The result retains the old spin factor and changes only its residual
multiplicity space. It therefore removes the exponential finite-group-table
constant from an iterative Schur--Clifford tower. It does not by itself prove
that all sequential corrections can be chosen coherently, nor that selector
sectors which do not activate the rank jump pay group-relator energy.

## Attempts

- `doubling-tape-from-self-similar-quantum-expander` proves the analytic
  implication once `self-similar-clifford-quantum-expander-tape` supplies the
  level-indexed expander words. The latter finite-presentation syntax is the
  only missing input for this one-step claim.
