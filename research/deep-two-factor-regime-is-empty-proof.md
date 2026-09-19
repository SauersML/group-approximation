---
rg: 2
id: deep-two-factor-regime-is-empty-proof
kind: route
title: The confined deep configuration contradicts the piece bound outright
target: deep-two-factor-regime-is-empty
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerDeepVacuity.lean
---

Machine-checked: `not_deep_confined` concludes `False`, so this is an
emptiness theorem rather than a case analysis with a favourable branch.

The configuration pins the block `M` simultaneously as a suffix of one
palindrome and, inverted, as a prefix of the adjacent one, while the depth
inequality `|c| + |t| < |M| + j` forces `M` to consume more of the first
relator than the conjugator can account for.  Under `C'(1/6)` those two
readings of `M` cannot both hold: the overlap they force between two
symmetrized relators exceeds the piece bound.  The minimality of the conjugacy
expression is what rules out the degenerate escape in which the two relators
coincide.

`not_deep_two_factor` is the packaged corollary, and both are stated for a
family of nonempty cyclically reduced relators satisfying
`MetricSmallCancellation R (1/6)`; there is no other hypothesis.

## Why the residual is not thereby closed

Because `DeepOverrunArc` assumes the negated prefix condition, which is exactly
the escape hatch from the configuration above.  A word whose block overruns the
whole adjacent palindrome is not confined, so `not_deep_confined` says nothing
about it.  Closing the deep lane means handling that case, and the emptiness
result is a reduction of its scope rather than a proof of it.

The sharp lane reuses this: `deepArcSourceSharp_of_deepOverrunArcSharp` routes
through the same `not_deep_confined`, which is why the `lambda`-parameterized
twins did not need an emptiness proof of their own.
