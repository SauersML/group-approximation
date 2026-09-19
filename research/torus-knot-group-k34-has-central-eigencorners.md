---
rg: 2
id: torus-knot-group-k34-has-central-eigencorners
kind: claim
title: "Every pair of corona unitaries X, Y with X^4 = Y^3 != 1 has an exact eigencorner of X^4, with eigenvalue other than 1, commuting with X and Y"
distinct_from:
  lifted-thompson-t-centre-has-commutant-eigencorners: that is the same conclusion only for the pairs that also satisfy the Thompson relators; this one is for all pairs and implies it (lifted-thompson-t-eigencorners-via-torus-knot-cover).
  commutant-projection-extraction: that is extraction for every countable group; this is its instance (K(3,4), x^4), a residually finite torsion-free one-relator group.
  torus-knot-group-k34-is-matricially-stable: that is a lifting statement which implies this; this asks only for the central spectral corner.
---

**OPEN.**  Let `Q` be a norm matrix corona, and let `X, Y in U(Q)` with
`X^4 = Y^3 =: u`.  If `u != 1`, then there are a nonzero projection
`P in {X, Y}' ∩ Q` and `lambda != 1` with `u P = lambda P`.

Equivalently, in matrices: for unitary `X_n, Y_n in U(k_n)` with
`||X_n^4 - Y_n^3|| -> 0` and `limsup ||X_n^4 - 1|| > 0`, there are
projections `P_n` with the following properties:
- `limsup ||P_n|| = 1`;
- `||[P_n, X_n]|| + ||[P_n, Y_n]|| -> 0`;
- `||(X_n^4 - lambda) P_n|| -> 0` for some `lambda != 1`.

By the diagonal lemma of `lifted-thompson-t-eigencorners-via-projection-extraction`,
applied to the group `K(3,4)`, approximate versions of these corners are
enough.

## Position in the graph

- It implies `lifted-thompson-t-centre-has-commutant-eigencorners` (route
  `lifted-thompson-t-eigencorners-via-torus-knot-cover`).
- It is implied by `torus-knot-group-k34-is-matricially-stable` (route
  `torus-knot-group-k34-central-eigencorners-via-stability`).
- **Where it already holds.**
  - When `sp(u)` has an isolated point `lambda != 1`: take the spectral
    projection.
  - When the pair lifts to exact pairs.
  - When `u` is a scalar in each block along a subsequence: take block
    projections.
- **How it could fail.**  The case left is a pair with the following
  properties:
  - `sp(X_n^4)` fills an arc;
  - every almost-commuting projection is spread over the arc;
  - `Y_n` moves the spectral subspaces of `X_n^4` by amounts that are small
    in each step but add up.

  This is the Voiculescu mechanism, carried into the free product
  `Z/4 * Z/3` of the fibres.  A counterexample here refutes only the
  torus-knot route to (EC), not (EC) itself.  The reason is that the
  counterexample pair need not satisfy the Thompson relators.

## Attempts

- 2026-09-19 swarm-0917-w16-w16-ptm-follow (stability-approximation).
  - Tried: through matricial stability of `K(3,4)` (route
    `torus-knot-group-k34-central-eigencorners-via-stability`).  This is
    complete except for that leaf, which is OPEN.
  - Tried: the direct spectral projection of `u = X^4`.  It works when
    `sp(u)` has an isolated point `lambda != 1`.  It dies when `sp(u)` is an
    arc.  Here `||[X_n^4, Y_n]|| -> 0`, since `u = Y^3` commutes with `Y`.
    But a sharp spectral cut of an almost-commuting normal element need not
    almost commute, and a smooth cut `f(u)` is not a projection.  This is
    the Voiculescu obstruction.
  - Deferred next attack: an arc real-rank-zero argument in
    `{X, Y}' ∩ Q`.  Alternatively, a Voiculescu-type counterexample with
    `X_n^4` near a rotation.
