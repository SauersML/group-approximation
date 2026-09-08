---
rg: 2
id: iwahori-flexible-repair-from-quadratic-steps
kind: route
title: Iterate the three-halves repair step to an exact compatible pair in one finite dimension
target: iwahori-local-global-defect-question
requires:
  - iwahori-uniform-quadratic-repair-step
  - quadratic-repair-steps-complete-in-finite-dimension
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

The class is the pairs of finite-dimensional unitary representations of the two
modular vertex groups, closed under adding trivial summands, and the defect is
`def` of the target node, which is `2L`-Lipschitz in the zero-padding metric by
`flexible-hs-metric-controls-words-and-padding`.  The first prerequisite is
exactly hypothesis `(RB1)` of the second for this class.

The second prerequisite therefore produces, from any pair with
`def(pi) <= min(eps, 1/(4A^2))`, an exactly compatible pair in a single finite
dimension at distance `O(sqrt(def(pi)))` in that metric.  Exactly compatible
means `pi_+|_(B_+) = pi_- o sigma`, i.e. a point of the compatible subvariety,
so the conclusion is `D(pi) <= 3.42 B sqrt(def(pi))`.

For `def(pi)` above the threshold the metric diameter bound `D(pi) <= 2` applies
(the compatible locus is nonempty -- it contains the trivial representation).
So the modulus

```text
f(x) = min( 3.42 B sqrt x, 2 ),      lim_(x -> 0) f(x) = 0,
```

works for every `pi` in `X_FD(Lambda)`, which is the statement of the target.

The dimension convention matches: the target's `d_2` is the generalized metric
that pads the smaller matrix with zero blocks, and the second prerequisite's
`d_0` is that same metric, so the exact pair produced in a possibly larger
dimension is an admissible comparison.  Strict same-dimension repair is not
claimed and is not what the target asks.
