---
rg: 2
id: unipotent-automata-over-finite-fields-are-surjective
kind: claim
title: Injective automata of the form identity plus higher-order terms over F_q are surjective over every group
distinct_from:
  sofic-groups-are-surjunctive: that proves every automaton surjective on sofic hosts; this asks for one normal-form class, the unipotent automata, on every host.
  gottschalk-surjunctivity-conjecture: that is every automaton on every host; this is only the unipotent normal form, and no equivalence with the conjecture is known.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

**OPEN.** Let `F = F_q` and `G` any group. Let `tau` be an injective automaton over `F^m`
whose normalized local rule is `x(g) + N(x)(g)`, where every monomial of `N` has total degree
at least 2. Suppose `tau` has a left inverse `sigma` with `deg sigma * deg tau < q`. Then
`tau` is surjective.

**Payoff.** Together with `low-degree-strict-pairs-have-one-sided-linear-parts`, every
low-degree strict automaton would come from a matrix one-sided inverse pair over `F_p[G]`
(`low-degree-strict-automata-force-matrix-kaplansky-failure`). The whole low-degree nonlinear
design space would collapse onto the Kaplansky and corner-fullness lanes.

## Attempts

- **Sofic hosts.** True there by `sofic-groups-are-surjunctive`, so the question lives on
  nonsofic hosts only.
- **Measure preservation.** `injective-measure-preserving-ca-is-surjective` would finish if
  unipotence forced `tau_* mu = mu`. The site marginal of `x(g) + N(x)(g)` is uniform when
  `N(x)(g)` is independent of `x(g)`, but `N` may read `x(g)` itself. Dies as stated.
- **Scaling torus.** For `q > 2`, conjugating by `x -> lambda x` gives the injective family
  `id + sum_j lambda^(j-1) N_j`. A finite field has no limit `lambda -> 0`, so no contraction.
  Dies.
- **Iterative solving.** `x = y - N(x)` has no contraction on a discrete alphabet. Dies.
- **Graded window counting.** Needs finite models, so it recovers only the sofic case.

Section 6 of the artifact.
