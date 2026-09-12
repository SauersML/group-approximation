---
rg: 2
id: strict-automata-copy-the-retract-poset-below-their-image
kind: claim
title: A strict automaton maps the poset of retract images isomorphically, with conjugacy, onto the retract images inside its image
distinct_from:
  strict-automata-closed-under-host-manipulations: that node shows host operations preserve strictness; this one shows a strict automaton makes every invariant of the retract-image lattice equal at the full shift and at a proper retract.
  retract-images-of-full-shifts-have-infinite-descending-chains: that node gives descending chains on every infinite group; this one is a self-similarity forced only by a strict automaton.
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Let `sigma o tau = id` for cellular automata on `A^G`, over any group `G`. For a retract image `X`
(the image of an idempotent automaton) put `Phi(X) = tau(X)`. Then:

- `Phi(X)` is a retract image: if `X = f(A^G)`, it is the image of the idempotent `tau f sigma`;
- `Phi` is injective, preserves and reflects inclusion, and `tau|_X` is a conjugacy `X -> Phi(X)`;
- `Phi` maps the retract images below any `X` onto the retract images below `tau(X)`. If `Y = g(A^G)`
  lies inside `tau(A^G)`, then `sigma g tau` is idempotent with image `sigma(Y)`, and
  `tau(sigma(Y)) = Y`.

So the poset of retract images with its conjugacy relation is isomorphic to its down-set at
`tau(A^G)`, and the top goes to `tau(A^G)`.

Consequence: every size defined as an invariant of the down-set of retract images, such as chain
heights, widths or lattice dimension functions, takes equal values at `A^G` and at the proper retract
`tau(A^G)` when `tau` is strict. Sizes intrinsic to the retract lattice can drop at the top only on
groups already known to be surjunctive, so they cannot certify surjunctivity of a nonsofic host.

Proof: artifact Section 2, route `strict-automata-copy-retract-poset-proof`.
