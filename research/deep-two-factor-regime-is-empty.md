---
rg: 2
id: deep-two-factor-regime-is-empty
kind: claim
title: The deep regime of a two-factor conjugacy expression is empty, so the deep residual survives only as an overrun past the adjacent palindrome
distinct_from:
  cascade-landing-from-deep-arc-and-beta: that records the assembled descent and its two residuals; this is a proved emptiness result about one of the regimes those residuals quantify over, and it strictly shrinks what `DeepArcSource` still has to cover.
artifacts:
  - GroupApproximation/Sofic/GreendlingerDeepVacuity.lean
  - GroupApproximation/Sofic/GreendlingerDeepVacuitySharp.lean
---

For a `C'(1/6)` family of nonempty relators, `not_deep_confined` proves
**`False`** from the deep configuration on a two-factor expression: if the
block `M` is confined to the adjacent palindrome, i.e.

```text
palindrome c t  = P' ++ M,
palindrome c' t' = invRev M ++ B',
|c| < |M|,  6j < |t|,  |c| + |t| < |M| + j,
```

then no such data exists.  The corollary `not_deep_two_factor` says no
two-factor minimal conjugacy expression is ever deep.

So the deep regime is not a case to be handled --- at the adjacent junction it
does not occur.

## What is left, and how it is stated

The surviving residual is `DeepOverrunArc`, and the way it escapes the
emptiness result is the hypothesis

```text
not (invRev M <+: palindrome c' t')
```

--- the block destroys **more** than the whole adjacent palindrome, so the
configuration `not_deep_confined` kills is not the one being assumed.  This is
worth stating carefully, because it is easy to read `DeepOverrunArc` as a
*conclusion* of the deep analysis.  It is not: it is an open hypothesis, and
what is proved is only that its confined counterpart is vacuous.

`deepArcSource_of_deepOverrunArc` and `deepTailArc_of_deepOverrunArc` are the
two consumers, and the sharp twin `DeepOverrunArcSharp` calls the *same*
`not_deep_confined`, so the emptiness result is shared by both forms of the
lane rather than duplicated.

## The shape of the gain

Before: `DeepArcSource` quantified over every deep configuration.  After: the
adjacent-junction ones are gone by theorem, and only the overrun ones remain.
That is a genuine narrowing of an open leaf, not a reformulation --- the
emptiness proof concludes `False` and consumes the metric hypothesis and
nothing else.
