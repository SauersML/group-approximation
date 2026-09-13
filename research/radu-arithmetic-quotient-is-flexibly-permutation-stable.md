---
rg: 2
id: radu-arithmetic-quotient-is-flexibly-permutation-stable
kind: claim
title: The cocompact arithmetic lattice Q in PGL_2(Q_2) x PGL_2(Q_2) under Radu's lattice is flexibly permutation-stable
distinct_from:
  radu-horizontal-quotient-is-arithmetic-lattice: that identifies Q; this asks whether its almost actions are Hamming-close to genuine ones
  hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable: that consumes flexible stability of SL_2(Z[1/p]); this is the same hypothesis for the quaternionic lattice under Radu's lattice
---

**OPEN.** Every sequence of almost actions of `Q` on finite sets, with relator defects tending to 0 in
normalized Hamming distance, is `o(1)`-close to genuine actions after padding by `o(1)` of the
points. `Q` is the lattice of `radu-horizontal-quotient-is-arithmetic-lattice`.

## Attempts

* **What it would give.** `radu-edge-coset-action-is-not-sofic`, through
  `radu-edge-coset-action-not-sofic-via-stability`. So the edge-lamp host route to soficity of
  Radu's metabelian quotient would be closed.
* **Contrapositive.** Suppose `radu-edge-coset-action-is-sofic`, and the uniform Cheeger constant
  holds. Then `Q` is not flexibly stable. So a positive construction would be an instability
  theorem for an irreducible lattice in a product of trees.
* **IRS obstruction: none expected (recalled, not re-read).**
  - For amenable groups, Becker–Lubotzky–Thom show flexible stability fails exactly when some IRS
    is not co-sofic.
  - Bader–Boutonnet–Houdayer–Peterson (charmenability of arithmetic groups of product type) give
    rigidity of characters and invariant random subgroups for irreducible `S`-arithmetic lattices
    of this shape. Every ergodic IRS should then be supported on finite-index subgroups or be
    trivial, and all such IRS are co-sofic.
  - So invariant random subgroups give no visible obstruction. Whether this applies to `Q` is not
    verified.
* **Status.** No stability theorem is known to this lane for lattices in products of trees, or for
  `SL_2(Z[1/p])`. See `no-published-unconditional-codense-stable-host` for the bounded search
  recorded on main.
* **Model test (recalled).**
  - *Satisfies it.* Free groups, trivially: every almost action is an action on the nose.
  - *Fails it.* Infinite residually finite groups with property (T) fail the strict form
    (Becker–Lubotzky).
  - `Q` has the Haagerup property, so that obstruction does not apply.
