---
rg: 2
id: thompson-v-surjunctive
kind: claim
title: Thompson's group V is surjunctive
root: true
refuted_by:
  - thompson-v-nonsurjunctive
distinct_from:
  thompson-v-not-sofic: that asks whether V admits sofic approximations; soficity would prove this claim by Gromov--Weiss, and a strict automaton over V would prove that one, but surjunctivity of V could hold with V nonsofic.
  leavitt-unit-group-surjunctive: that is surjunctivity of the Leavitt unit group, which contains V and would give this claim; this is the smaller group, which is not known to decide that one.
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
  - research/artifacts/surjunctivity-permanence-envelope-2026-09-12.md
---

**OPEN.** For every finite alphabet `A`, every injective cellular automaton
`A^V -> A^V` over Thompson's group `V = G_(2,1)` is surjective.

*Marked `root` because it is a question in its own right, unrecorded before
2026-09-12.* A strict automaton over `V` would give a nonsofic `V`
(`thompson-v-not-sofic`) and refute Gottschalk's conjecture over the Leavitt
unit group, since `V <= R^x`.

## Attempts

- **Soficity.** If `V` is sofic, `sofic-groups-are-surjunctive` proves this.
  `thompson-v-not-sofic` is open, with no mechanism in either direction.
- **Permanence.** `V` is finitely presented, infinite and simple
  (`thompson-v-finitely-presented-infinite-simple`). By
  `gottschalk-counterexamples-lie-outside-the-permanence-closure`, it lies in the
  permanence closure of the sofic groups exactly when it is sofic. So the landed
  permanence theorems add nothing beyond the soficity question.
- **Coset peeling through the Cantor action.** Dead:
  `thompson-v-surjunctive-via-coset-peeling`. Every stabilizer group the method
  offers contains a copy of `V`.
- **Cantor-orbit encodings.** Dead in general by
  `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`.
- **Route through the Leavitt units.** `thompson-v-surjunctive-from-leavitt-units`
  is valid but needs the harder `leavitt-unit-group-surjunctive`.
- **What is left.** An argument over `V` itself, for automata whose memory
  generates `V`, perhaps an induction on the automaton using `V_U ~= V` on
  disjoint clopens. None is known: Section 4 of the artifact.
- **Negative dual (2026-09-12).** `thompson-v-nonsurjunctive` refutes this claim. Its linear
  target is `thompson-v-ternary-swap-idempotent-is-full`.
- **Soficity route.** `thompson-v-surjunctive-from-soficity`, through the open
  `thompson-v-is-sofic`.
- **Self-similar descent.** Dead in its rewrite form:
  `thompson-v-surjunctive-via-self-similar-descent`, killed by
  `v-self-similar-rewrites-preserve-strict-pairs`. Conjugating the memory into `V_U ~= V`, or
  splitting it along disjoint clopens, keeps the rules and both tables, so nothing decreases.
- **Cantor-local arguments (2026-09-17).** Obstruction:
  `compressible-base-controlled-automata-are-strict`. Let the local rule read which
  cell of a clopen partition contains the Cantor point of the site. The
  compression `T(z) = 0z`, given piecewise by two elements of `V`, then yields
  injective automata that are non-surjective on every fibre. So induction on
  clopens with `V_U ~= V`, germ-wise peeling, transfers through the groupoid
  `C x| V`, and quasi-invariant weighted counting all prove a false statement.
  The same holds over `F_2` with its boundary, which is surjunctive. Amenable
  minimal bases calibrate correctly. A proof must spend `tau_x = tau_(gx)` for
  `g` moving `x`, not only commutation with stabilizers. This sharpens
  "What is left" above.
- **Coinvariant rank counting (2026-09-17).** Dead. A strict pair makes
  `A^G` conjugate to a proper subshift `Y`, so `C(Y,Z)` is a proper
  `Z[G]`-quotient of `C(A^G,Z)` isomorphic to it. A contradiction would need
  `H_0(G; C(A^G,Z)) ⊗ Q` to be finite-dimensional, as it is for finite `G`
  (pigeonhole). For every infinite `G` it is infinite-dimensional, because
  Bernoulli marginals and pattern frequencies give infinitely many independent
  invariant functionals. The rank comparison therefore carries no information.
