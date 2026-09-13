---
rg: 2
id: zaremsky-2-01-thompson-f-amenable
kind: claim
title: "Zaremsky Problem 2.1 resolved: is Thompson's group F amenable?"
root: true
distinct_from:
  thompson-f-is-amenable: that claim is the affirmative answer; this is the question, established by either answer.
  thompson-f-is-not-amenable: that claim is the negative answer; this is the question, established by either answer.
  thompson-f-amenable-iff-group-ring-is-ore: that is an established reformulation of amenability as the Ore condition in K[F]; this is the question as posed on Zaremsky's list, which that reformulation does not answer.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2 (Thompson groups),
Problem 1, verbatim: "Is Thompson's group F amenable?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-01-by-yes` requires `thompson-f-is-amenable`.
- **No**: `zaremsky-2-01-by-no` requires `thompson-f-is-not-amenable`.

Never write a `requires: []` route into this claim. As a bare disjunction the
statement is a classical tautology; its content is knowing which answer holds.

**Reading.** `F` is Richard Thompson's group: the orientation-preserving
piecewise-linear homeomorphisms of `[0,1]` with finitely many breakpoints, all
at dyadic rationals, and slopes powers of 2. Amenability is the existence of a
left-invariant mean on `l^infinity(F)`. It is equivalent to Følner sets for a
finite generating set, to `||P|| = 1` for the simple random walk (Kesten), and to
the Ore condition in `K[F]` for every field `K`
(`thompson-f-amenable-iff-group-ring-is-ore`). The question has been open since
R. Geoghegan raised it in 1979. The two answers were already recorded in this
graph as roots by the 2026-09-12 lane `thompson-f-amenability`
(`research/artifacts/thompson-f-amenability-map-2026-09-12.md`); this root
wires Zaremsky's numbered problem to them and adds no mathematics of its own.

Unconditional constraints already established in the graph:

- no free subgroups, not elementary amenable (`thompson-f-has-no-free-subgroups`);
- `C^-n`-Følner sets have at least `exp_n(0)` elements (Moore,
  `thompson-f-folner-function-exceeds-every-tower`);
- finitely supported strictly non-degenerate random walks are not Liouville
  (Kaimanovich, `thompson-f-random-walks-are-not-liouville`);
- not strongly amenable (`thompson-f-is-not-strongly-amenable`);
- finitely many exact closed-walk counts never certify non-amenability
  (`thompson-f-moment-data-cannot-certify-nonamenability`), while they do certify
  `||P|| > 0.880541` (`thompson-f-random-walk-norm-certified-lower-bound`);
- large classes of pairs in `K[F]` have common multiples
  (`thompson-f-binomial-pairs-have-common-multiples`,
  `thompson-f-one-bump-binomials-have-common-multiples`, Guba's Question 3.20
  answered as `thompson-f-one-minus-x1-is-ore-with-every-element`).

## Attempts

- 2026-09-13, lanes `z2-01-f-nonamenable` (non-amenability) and
  `z2-01-f-amenable` (amenability): open-status check for work after the list's
  date, then new certificate classes on each side. The detailed attempt logs
  live on the two answer claims, `thompson-f-is-amenable` and
  `thompson-f-is-not-amenable`.
