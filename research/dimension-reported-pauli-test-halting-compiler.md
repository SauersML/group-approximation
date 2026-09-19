---
rg: 2
id: dimension-reported-pauli-test-halting-compiler
kind: claim
title: A halting output dimension activates a uniformly sound Pauli braiding test
distinct_from:
  dimension-reported-clifford-table-halting-compiler: that asks for the complete multiplication table of an extraspecial group; this asks only for the succinct constant-robust Pauli braiding verifier.
---

Construct a total computable machine-to-group compiler which also outputs
computable rationals `delta_M>0` and `alpha_M<sqrt(2)`, satisfies `(IMK1)`,
and has the following clause. If the source machine halts and outputs `D`, it
computes `N` satisfying `(PBD2)`. Every `D`-dimensional tuple for the compiled
finite presentation with relator defect below `delta_M` and marked distance
above `alpha_M` must
produce a finite-dimensional strategy for the perfect-complete `N`-qubit
Pauli braiding test with success at least `1-eta_0` and local dimension at
most `D`.  This contradicts `(PBD1)` and proves `(DMK2)` in the reported
dimension.

The translation from normalized-HS relator energy to rejection probability,
and the activation after the halting computation, may lose a computable
factor depending on the source code `M`. It must remain independent of `N`,
`D`, and the unknown runtime. In the nonhalting case the compiled group must
have an exact model in which the marked word remains nontrivial.

## Attempts

- This removes the exponentially large all-pairs table from the semantic
  target.  The verifier uses only BLR linearity, consistency and Magic-Square
  anticommutation templates, with constant robustness.
- A normalized trace tuple canonically gives a maximally-entangled strategy:
  left action on one player and transpose/right action on the other turn
  state-dependent squared errors into normalized-HS squared errors.  This is
  now the exact theorem
  `maximally-entangled-vectorization-is-hs-isometry`.  The question-indexed
  observables still have to be represented by finitely many group words; that
  remaining syntax is isolated as `uniform-halting-pauli-word-oracle`.
- Directly naming all questions makes the finite presentation depend on the
  post-halting value `N`; ordinary machine simulation reintroduces runtime
  telescoping.  A finite oracle/tape action must make uniformly sampled BLR
  checks conjugates of finitely many group-word templates.
- Dinur gap amplification explains how local inconsistency can have constant
  density, while recursive compression explains runtime independence.  The
  unresolved theorem is their perfect-complete group-word realization for
  this especially structured Pauli verifier.
- The instance-modulated Kleene lemma permits a source-dependent quantitative
  constant such as the `C_m` in a computable BCS family. It does not permit a
  modulus discovered only after the source machine halts, so ordinary
  runtime-length telescoping remains insufficient.
- Allowing the modulus to be an arbitrary positive function of the reported
  dimension does not repair this. By
  `dimension-kleene-threshold-needs-amplification-envelope`, the
  canonical microstate defect may approach zero more slowly than that
  function, even after tensor amplification. Thus the present independence
  from `N,D`, and runtime may be weakened only to a quantitatively positive
  amplification envelope, not to pointwise positivity.
