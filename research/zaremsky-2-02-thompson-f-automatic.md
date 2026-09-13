---
rg: 2
id: zaremsky-2-02-thompson-f-automatic
kind: claim
title: "Zaremsky Problem 2.2 resolved: is Thompson's group F automatic?"
root: true
distinct_from:
  thompson-f-is-automatic: that is the affirmative answer; this is the question, established by either answer
  thompson-f-is-not-automatic: that is the negative answer; this is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2 (Thompson groups),
Problem 2, verbatim: "Is F automatic?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-02-by-yes` requires `thompson-f-is-automatic`.
- **No**: `zaremsky-2-02-by-no` requires `thompson-f-is-not-automatic`.

Never write a `requires: []` route into this claim.

## Reading

`F` is Richard Thompson's group: the orientation-preserving piecewise-linear
homeomorphisms of `[0,1]` with finitely many breakpoints, all at dyadic
rationals, and slopes powers of 2. It has the finite presentation
`< x0, x1 | [x0 x1^-1, x0^-1 x1 x0], [x0 x1^-1, x0^-2 x1 x0^2] >`
(Cannon–Floyd–Parry).

"Automatic" is in the sense of Epstein, Cannon, Holt, Levy, Paterson and
Thurston, *Word Processing in Groups* (1992): a finite generating set `A` and a
regular language `L` over `A ∪ A^-1` that maps onto the group, such that for
every `a ∈ A ∪ {1}` the set of pairs `(u, v) ∈ L × L` with `ū a = v̄` is accepted
by a synchronous two-tape finite automaton. Equivalently, `L` is regular, maps
onto the group, and has the synchronous fellow traveller property.

Standard facts from that book, used here without re-reading theorem numbers:

1. automaticity does not depend on the finite generating set;
2. an automatic group has an automatic structure with uniqueness (one accepted
   word per element);
3. in an automatic structure with uniqueness there is `N` with
   `|w| <= N |w̄| + N` for every accepted `w`. The pumping argument: if the
   unique representative of `g a` ran for more than `N` steps past the length of
   the representative of `g`, two of those steps would share an automaton state
   and a position in the `K`-ball around `g`, and cutting the loop between them
   would give a second accepted word for `g a`.

So a positive answer is a regular language over `{x0^±1, x1^±1}` with
uniqueness and the fellow traveller property. A negative answer must exclude
every such language, including those whose words are only multiplicative
quasigeodesics.

Not asked: biautomaticity, asynchronous automaticity, or graph automaticity in
the sense of Kharlampovich–Khoussainov–Miasnikov.

## What is known (arXiv abstracts read 2026-09-13)

- V. Guba, arXiv:math/0211395: the Dehn function of `F` is quadratic. Automatic
  groups have quadratic Dehn functions, so this obstruction is absent.
- S. Cleary, M. Elder, J. Taback, arXiv:math/0410616 (J. Algebra 303 (2006)
  476–500): over the standard generating set `F` has infinitely many cone types
  and no regular language of geodesics.
- M. Elder, J. Taback, arXiv:1501.04313: `F` is 1-counter graph automatic. The
  abstract opens "It is not known whether Thompson's group F is automatic."
- J. Taback, S. Younes, arXiv:1501.04315: a 3-counter graph automatic structure
  built from caret types.
- J. Hauze, arXiv:1801.01965: over `{x0^±1, x1^±1}`, a language that accepts,
  for every element, at least one word within a fixed additive constant of a
  geodesic cannot be part of an automatic structure for `F`.
- `F` is of type `F_∞` (Brown–Geoghegan 1984), so the finiteness obstruction
  is absent too.

By fact 3, Hauze's theorem is the additive case over one generating set. The
multiplicative case, over all generating sets, is the whole problem.

## Attempts

- 2026-09-13 (lane z2-02-f-automatic): the classical consequences of
  automaticity (finite presentation, quadratic Dehn function, type `F_∞`) all
  hold for `F`, and geodesic and near-geodesic structures over the standard
  generators are already excluded. The open ground is (a) structures whose
  words have unbounded additive excess over geodesic length, and (b)
  generating-set-free invariants of automatic groups that `F` might violate.
  The first such candidate is infinite cohomological dimension; see
  `thompson-f-is-not-automatic`.
