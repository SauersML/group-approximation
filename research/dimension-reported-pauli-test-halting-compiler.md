---
rg: 2
id: dimension-reported-pauli-test-halting-compiler
kind: claim
title: A halting output dimension activates a uniformly sound Pauli braiding test
distinct_from:
  dimension-reported-clifford-table-halting-compiler: that asks for the complete multiplication table of an extraspecial group; this asks only for the succinct constant-robust Pauli braiding verifier.
  zpc-selector-sound-lcs-compiler: that lowers arbitrary tailored readable control to linear constraints; this only has to lower the fixed BLR-linearity and Magic-Square templates of the Pauli test.
---

Construct a total computable machine-to-group compiler with universal
`delta>0` and `alpha<sqrt(2)` satisfying `(DMK1)` and the following clause.
If the source machine halts and outputs `D`, it computes `N` satisfying
`(PBD2)`.  Every `D`-dimensional tuple for the compiled finite presentation
with relator defect below `delta` and marked distance above `alpha` must
produce a finite-dimensional strategy for the perfect-complete `N`-qubit
Pauli braiding test with success at least `1-eta_0` and local dimension at
most `D`.  This contradicts `(PBD1)` and proves `(DMK2)` in the reported
dimension.

The translation from normalized-HS relator energy to rejection probability,
and the activation after the halting computation, must have constants
independent of `N`, `D`, and runtime.  In the nonhalting case the compiled
group must have an exact model in which the marked word remains nontrivial.

## Attempts

- This removes the exponentially large all-pairs table from the semantic
  target.  The verifier uses only BLR linearity, consistency and Magic-Square
  anticommutation templates, with constant robustness.
- A normalized trace tuple canonically gives a maximally-entangled strategy:
  left action on one player and transpose/right action on the other turn
  state-dependent squared errors into normalized-HS squared errors.  This is
  the natural local lowering, but the question-indexed observables still have
  to be represented by finitely many group words.
- Directly naming all questions makes the finite presentation depend on the
  post-halting value `N`; ordinary machine simulation reintroduces runtime
  telescoping.  A finite oracle/tape action must make uniformly sampled BLR
  checks conjugates of finitely many group-word templates.
- Dinur gap amplification explains how local inconsistency can have constant
  density, while recursive compression explains runtime independence.  The
  unresolved theorem is their perfect-complete group-word realization for
  this especially structured Pauli verifier.

