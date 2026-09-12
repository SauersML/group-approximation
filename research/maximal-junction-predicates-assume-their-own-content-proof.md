---
rg: 2
id: maximal-junction-predicates-assume-their-own-content-proof
kind: route
title: Read the binder list, then prove the predicate from the metric condition
target: maximal-junction-predicates-assume-their-own-content
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerLandingProd.lean
  - GroupApproximation/Sofic/GreendlingerSharpTwins.lean
---

Two independent confirmations, one syntactic and one machine-checked.

**Syntactic.**  Both definitions quantify over `c t c' t' x` with the
domination `c'.length <= c.length`, and both state
`IsPiece (symmetrization R) (t.take x) or x = 0` implies a bound mentioning
only `t` and `x`.  Substituting anything for `c`, `c'`, `t'` changes neither
side.  A predicate whose stated content is invariant under its configuration
data is not a statement about that configuration.

**Machine-checked.**  `maximalJunctionSharp_of_metric` derives the sharp
predicate from `MetricSmallCancellation R lam` with `0 < lam <= 1/6` and
nonempty relators, by applying the metric condition to `t.take x` --- legal
because `List.take_prefix` gives `t.take x <+: t` with no hypothesis --- and
closing the `x > |t|` corner by `List.length_take` and arithmetic.  No open
residual is consumed.  The half form admits the same one-line proof from
`GreendlingerPiece.six_mul_length_lt_of_isPiece`; that proof is not written,
which is the only asymmetry between the two.

**Unconsumed.**  A repository-wide search for both names returns twelve
occurrences: the two definitions, one use as the goal of the theorem above,
and nine mentions inside docstrings.  No declaration takes either as a
hypothesis.  So the vacuity costs nothing downstream --- it cost only the
belief that a residual was being tracked.

## Why the record is kept rather than the definitions deleted

Because the trap is the finding.  The intent was correct and is still the
right target; what failed was writing a predicate for it without the junction
configuration --- which palindrome, which cancellation, what "destroyed"
names.  Inventing a plausible-looking predicate without that data is exactly
the failure mode, and a deleted definition records nothing.  The sharp file
says so in its own demotion note, and keeping the pair visible is what stops
the same predicate being re-derived from the same intent.

## What would count as progress

A theorem concluding `IsPiece (symmetrization R) (t.take x)` from the junction
configuration plus `c'.length <= c.length`.  Until such a statement exists,
any claim to have advanced the maximal-conjugator route should be read against
this node first.
