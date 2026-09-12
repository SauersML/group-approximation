---
rg: 2
id: stabilized-two-chart-reynolds-word-transport
kind: claim
title: A stabilized recursive packet tail exposes one uncompensated local Reynolds gap in finite matrices
distinct_from:
  forbidden-packet-reynolds-holonomy-payment: that is the analytic payment once a stabilized return has been built; this constructs the stabilized algebraic return and extracts the local residue.
  trace-functorial-bcs-signal-groupification-impossible: that rules out a decoder surviving in every trace; here the infinite tail absorbs the rank jump in the regular/infinite model and only finite matrix multiplicities expose the residue.
---

For every fixed predicate packet `A_f<B_f`, construct a finitely generated
recursively presented stabilized group with:

1. a countable packet tail and a compressor identifying two **isomorphic
   stabilized** subgroups, never the raw nonisomorphic tables `A_f,B_f`;
2. a faithful infinite-dimensional marked representation in which the tail
   absorbs the finite multiplicity jump, so the marked selector word remains
   nontrivial;
3. a decidable word problem with a polynomial time/relative-area bound, so
   `quantitative-higman-embedding-with-dehn-control` embeds the construction
   in a finitely presented host and
   `subgroup-dehn-function-is-the-hyperlinearity-modulus` controls every
   derived level relation;
4. a two-chart local window whose exactified finite-dimensional restriction
   cancels all tail boundary terms but one copy of `R_A-R_B`; and
5. a sparse estimate bounding the resulting local Reynolds-channel transport
   error by `p(n)` times the host relator defect, with `p` polynomial and with
   the shared self-referential BCS selector tuple retained.

Then `forbidden-packet-reynolds-holonomy-payment` makes the surviving local
rank gap pay normalized-HS energy, while the infinite model avoids the
trace-functorial regular-representation contradiction.

## Attempts

- **Raw finite-table conjugacy. Dead.** It is ruled out by
  `termwise-finite-reynolds-holonomy-has-zero-rank-gap`.
- **Eilenberg-swindle tail. Active.** Take a common central product of one
  baseline packet and countably many full predicate packets. Map the baseline
  packet into the `A_f` subgroup of the first full packet and shift every full
  packet one step. This is an injective self-embedding and gives the right
  infinite absorption. A finite prefix, however, has a compensating boundary
  packet; the open calculation is to use the `P/Q` chart switch and the
  Fanizza oriented recurrence so that geometric weighting cancels that far
  boundary while leaving the level-zero `R_A-R_B` term.
- **Logical gate.** The construction must use the shared contextual BCS tuple,
  not merely a scalar forbidden-mass lower bound, or
  `multiplicity-surplus-is-blind-to-the-non-ce-input` supplies a false
  classically-unsatisfiable instance.
- **Spectral replacement.** `property-t-hs-positive-density-commutant-no-growth`
  shows that it is unnecessary to return the raw finite Reynolds averages.
  It is enough to place their difference as low compressed spectrum
  transverse to the original low spectrum. The sharper remaining target is
  `schur-packet-as-positive-density-compressor-wall`.
- **The raw Jacobi braid is an extensive boundary term.**  The exact
  calculation in `jacobi-drifted-braid-defect-is-extensive` shows that
  drifting both rank-one root parameters sends the `S_3` braid to two words
  differing on `2(N-1)` of the `2N` coefficient dimensions.  Hence the
  proposed `P/Q` switch does not leave only a far one-qubit boundary after a
  closed upper/lower cycle.  A stabilized swindle must cancel this explicit
  extensive braid cocycle before the Reynolds telescoping in item 4 can even
  be formulated.
- Duplicating the parabolics is not a substitute for that cancellation:
  `braid-free-two-chart-actor-is-amenable` computes the separated actor as a
  metabelian group and rules out relative `(T)` for its infinite Weyl tape.
  The stabilized tail must retain mixed rank-one action while cancelling the
  explicit braid defect.
