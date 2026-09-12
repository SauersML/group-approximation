---
rg: 2
id: closed-local-rules-have-uniform-hitting-or-infinite-safe-tail
kind: claim
title: A closed finite-range recursion has either a uniform hitting horizon or an infinite safe tail
distinct_from:
  contractive-computation-ladder: that gives a sufficient scalar contraction once a recurrence is proved; this is the compactness obstruction to obtaining no-tail soundness from arbitrarily long locally safe finite runs.
  hyperlinear-radical-is-finitely-witnessed: that concerns matrix-ultraproduct word death for an r.e. group presentation; this is the underlying topological finite-range recursion lemma before any group or matrix model is chosen.
---

Let `X` be compact, let `I,A subset X` be closed, and let
`C subset X^(r+1)` be a closed finite-range rule. Exactly one of the following
alternatives holds.

1. There is a uniform `N` such that no length-`N` trajectory starts in `I`,
   remains in `A`, and satisfies every local `C`-window.
2. There is an infinite trajectory starting in `I`, remaining in `A`, and
   satisfying every local `C`-window.

Thus a closed self-similar rule cannot have arbitrarily late first failure
without an infinite or nonstandard safe tail. A proposed recursive challenge
library needs a genuine finite feedback/capacity mechanism; a countable
disjunction saying that some ever-later local test fails is not a no-tail
theorem.
