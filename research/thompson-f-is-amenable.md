---
rg: 2
id: thompson-f-is-amenable
kind: claim
title: Thompson's group F is amenable
root: true
distinct_from:
  thompson-f-is-not-amenable: that is the opposite answer to the same named problem; this is the amenable answer, which would force the Følner function of F to outgrow every fixed tower of exponentials.
  thompson-v-hyperlinear: that asks whether V embeds into a tracial matrix ultraproduct; this asks whether the subgroup F of V admits Følner sets, a strictly stronger approximation property for F.
---

**OPEN.** Richard Thompson's group `F` is amenable. `F` is the group of
orientation-preserving piecewise-linear homeomorphisms of `[0,1]` with finitely
many breakpoints, all at dyadic rationals, and slopes powers of 2.

*Marked `root` because it answers a named open problem.* Survey of the current
state: V. Guba, *Amenability problem for Thompson's group F: state of the art*,
arXiv:2305.07113v4 (19 Oct 2023), J. Groups Complexity Cryptology 15 (2023).
The two answers are recorded as two roots: this one and `thompson-f-is-not-amenable`.

Unconditional constraints in this graph:
- `thompson-f-has-no-free-subgroups`: `F` has no free subgroups and is not
  elementary amenable, so neither answer follows from a classical criterion.
- `thompson-f-folner-function-exceeds-every-tower`: a `C^-n`-Følner set has at
  least `exp_n(0)` elements.
- `thompson-f-random-walks-are-not-liouville`: finitely supported non-degenerate
  random walks have non-trivial Poisson boundary.
- `thompson-f-is-not-strongly-amenable`.
- `thompson-f-amenable-iff-group-ring-is-ore`: amenability is the Ore condition
  for `K[F]`.

Source map: `research/artifacts/thompson-f-amenability-map-2026-09-12.md`.

## Attempts

- **Explicit Følner families.** Any construction has to beat
  `thompson-f-folner-function-exceeds-every-tower`. A family whose size is
  bounded by a fixed tower `exp_k` in `1/epsilon` cannot be Følner for small
  `epsilon`. Balls and bounded-depth forest-diagram families have elementary
  growth. Dies: every explicit family of bounded recursive complexity is excluded,
  so a witness must come from a non-elementary recursion or a non-constructive
  argument.
- **Liouville measures.** By the Kaimanovich–Vershik and Rosenblatt criterion,
  amenability is equivalent to the existence of a non-degenerate symmetric
  measure with trivial Poisson boundary.
  `thompson-f-random-walks-are-not-liouville` excludes every strictly
  non-degenerate finitely supported measure. Dies: only infinitely supported
  measures remain, and none is known to be Liouville and non-degenerate.
- **Group-ring equations.** By `thompson-f-amenable-iff-group-ring-is-ore`,
  amenability is the Ore condition for `K[F]`: every pair of nonzero `a, b` has a
  nonzero common multiple. Dies: a universally quantified algebraic statement,
  with no structural source of common multiples. Guba's survey treats equations
  in the group ring of `F`, and this graph records only its abstract.
- **Ramsey reformulation.** J. T. Moore, *Amenability and Ramsey theory*, Fund.
  Math. 220 (2013) 263–280, reformulates amenability as a structural Ramsey
  statement that "constitutes a considerable weakening of the Følner criterion"
  (abstract). Neither the precise statement for `F` nor the status of Moore's
  nonassociative Hindman program (arXiv:1209.2063) has been read into this graph.
  Dies here for lack of a verified statement, not for a mathematical reason.
- **Strong amenability.** `thompson-f-is-not-strongly-amenable`: `F` has a
  proximal action without fixed points, so no argument through strong
  amenability can work.
- **This graph's compression rigidity.** `F` lies in `V`, which has the Haagerup
  property (`thompson-v-has-haagerup-property`, whose source covers `F`), so by
  `a-t-menable-groups-have-no-rigid-compression-defect` `F` carries no rigid
  compression defect. Those tools decide soficity questions for Kazhdan pairs.
  Dead for amenability in both directions.
