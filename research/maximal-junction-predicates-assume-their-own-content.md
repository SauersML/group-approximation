---
rg: 2
id: maximal-junction-predicates-assume-their-own-content
kind: claim
title: Both maximal-junction predicates are vacuous -- they assume the piece-ness their intent was to establish, and the statement that carries the maximal-conjugator argument is written nowhere
distinct_from:
  piece-overlap-right-is-exactly-dehn-swap-closure: that is a reduction that turned out to move no strength but whose statement is still the right one; this is a predicate whose STATEMENT is wrong -- it assumes its own content, so discharging it would close nothing at all.
  sharp-form-layer-supplies-the-arc-budget: that layer twinned the live lane at the sharp constant; this records the one thing it twinned faithfully and should not have, since the half form it copied was already defective.
artifacts:
  - GroupApproximation/Sofic/GreendlingerMaxConjugator.lean
  - GroupApproximation/Sofic/GreendlingerSharpTwins.lean
  - GroupApproximation/Sofic/GreendlingerLandingProd.lean
---

`MaximalJunction` (half form) and `MaximalJunctionSharp` (sharp twin) were
carried as word-combinatorial residuals of the maximal-conjugator argument.
Both are vacuous.  Each takes

```text
IsPiece (symmetrization R) (t.take x)  or  x = 0
```

as a **hypothesis** and concludes only a numeric bound on `x` --- `6x < |t|`
in the half form, `x < lam*|t|` in the sharp one.  But `t.take x` is a prefix
of `t` unconditionally, so `MetricSmallCancellation` already gives that bound
for any piece whatever.  The conclusion follows from the metric condition
alone.

`maximalJunctionSharp_of_metric` proves this outright: from nonempty relators,
`0 < lam <= 1/6` and `C'(lam)`, `MaximalJunctionSharp R lam` holds.  Its proof
binds four of its eight arguments as `_c`, `_c'`, `_t'`, `_hle` --- machine-
checkable evidence that the configuration plays no part.

## The tell, and why it is the badge-strength failure mode

`c`, `c'`, `t'` and the conjugator domination `c'.length <= c.length` appear in
neither the hypothesis nor the conclusion.  Four of the eight binders cannot
influence the statement, and those four are exactly what the intent turns on.
A predicate can look like the hard residual, be named after it, be twinned
faithfully at a second constant, and still say something that follows in one
line --- which is the whole of the badge-claim-strength failure mode: a TRUE
statement standing in for the one that was meant.

## What is actually missing

The load-bearing statement is word-level and comes *before* the numeric step:
at such a junction the destroyed part of the rotation **is** `t.take x`, and
**is** a piece, as a consequence of the conjugator domination.  That statement
does not exist anywhere in the repository --- not as a theorem, not as a
residual definition, not as an axiom.  The domination hypothesis
`c'.length <= c.length` occurs only inside the two vacuous definitions.

The nearest genuine thing is `eaten_lt_of_long_next_conjugator`, which does
*derive* piece-ness rather than assume it --- but for the opposite domination
(the neighbouring conjugator is the longer one) and under a five-twelfths
survival hypothesis, so it is a different configuration.

## Consequences, stated exactly

- Discharging either predicate closes nothing.
- Nothing is lost by their being open: **no declaration anywhere takes either
  as a hypothesis.**  They are unconsumed, and so are the two theorems named
  after them, `greendlingerAt_of_maximalJunction` and
  `greendlingerAtSharp_of_maximalJunctionSharp`, which are unused aliases of
  the two-pieces lemmas.  Neither predicate is reachable from
  `SharpGreendlingerGate`, `GreendlingerConclusion`, `CascadeLanding` or the
  router conclusions; the live lane runs through `DeepArcSourceSharp` and the
  beta side.
- So this is a documentation and roster hazard, not a hole in the program.

## The correction is only two-thirds applied

`GreendlingerSharpTwins` section 6 and `GreendlingerLandingProd` section 12
both state the vacuity plainly and self-critically.  `GreendlingerMaxConjugator`
does **not**: its header still calls `MaximalJunction` "the one
word-combinatorial fact the argument consumes", still says "Unconditional
except where `MaximalJunction` is named" (it is named nowhere but its own
definition), and its definition's docstring still ends "This is the whole of
what is not yet proved."  By the repository's own audit that sentence is false
twice over: the predicate is a triviality, and what is genuinely unproved is
written nowhere.  Two notes files carry the same stale reading.
