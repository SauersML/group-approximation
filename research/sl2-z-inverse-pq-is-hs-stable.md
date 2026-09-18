---
rg: 2
id: sl2-z-inverse-pq-is-hs-stable
kind: claim
title: SL2(Z[1/pq]) is Hilbert--Schmidt stable
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
refuted_by:
  - sl2-z-inverse-pq-is-not-strictly-hs-stable
distinct_from:
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that consumes stability of a lattice such as SL2(Z[1/p]) through a central extension; this asks for stability of the three-place lattice SL2(Z[1/pq]), consumed through the Pauli lamplighter over its subgroup SL2(Z[1/p]) with no central extension.
---

Show that `SL_2(Z[1/pq])` (`p != q` primes) is HS-stable in the
same-dimension sense: for every `eps > 0` there is `delta > 0` such that
every finite-dimensional unitary tuple with relator defect below `delta`
is within `eps` (normalized HS, on generators) of an exact unitary
representation.

By `sl2-s-arithmetic-pair-is-codense-kazhdan` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, this makes the
finitely presented HNN extension `G_(p,q) = <SL_2(Z[1/pq]), t | [t,
SL_2(Z[1/p])] = 1>` an explicit nonhyperlinear group (flexible stability
suffices).  Conversely, hyperlinearity of `G_(p,q)` would refute this claim.

This is the same kind of question as Dogon--Vigdorovich's stability of
`SL_2(Z[1/p])`, one prime further along: the group is an irreducible
lattice in `SL_2(R) x SL_2(Q_p) x SL_2(Q_q)`, has (T;FD) but not (T), is
residually finite, has the congruence subgroup property, and its
finite-dimensional unitary representations all factor through congruence
quotients.  Because it is hyperlinear and residually finite, stability is
not excluded by `hyperlinear-hs-stable-is-residually-finite`, and because
it lacks (T) it is not excluded by
`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`.

## Attempts

- **Amalgam/tree structure.**  `SL_2(Z[1/pq])` acts on the product of the
  `p`- and `q`-adic trees; vertex stabilizers are conjugates of
  `SL_2(Z[1/q])` and `SL_2(Z[1/p])`, which are (T;FD) but whose own
  stability is Dogon--Vigdorovich's open question.  An approximate
  representation restricts to approximate representations of the vertex
  groups; even granting their stability, the two exact representations
  obtained must be glued along the edge groups, and local rigidity of the
  edge group representations is what is missing (the `iwahori-*` lane
  studies exactly this gluing for `SL_2(Z[1/p]) = SL_2(Z) *_B SL_2(Z)`).
- **(T;FD) against deformation.**  Stability needs approximate
  representations near the finite congruence representations not to
  deform away; (T;FD) gives the isolation of the trivial representation
  and of each congruence representation among finite-dimensional ones,
  but not a uniform modulus against approximate representations of
  growing dimension, which is the content of the claim.
- **What would refute it.**  A family of approximate representations of
  `SL_2(Z[1/pq])` with defect tending to zero and bounded distance from
  all exact ones; by the tensor trick in
  `stable-group-with-codense-kazhdan-subgroup` such a family could be
  taken with traces tending to the canonical trace, so it would also
  refute the weaker microstate-stability.
- **2026-09-17, swarm-0917-w6-w6-nh-last2: REFUTED (same-dimension notion).**
  The second attempt above stops one step short.  (T;FD) does give a
  uniform modulus, but it points the other way.
  - *The tuple.*  Take the Steinberg representation `St_l` of `SL_2(F_l)`,
    `l` a prime not dividing `pq`, pulled back along the surjection
    `SL_2(Z[1/pq]) -> SL_2(F_l)`.  Compress it to the orthocomplement of one
    unit vector and replace each generator by the unitary polar part.  The
    relator defect is `O(l^(-1/2))`.
  - *The invariant.*  For any exact `rho` of dimension `l - 1`, consider the
    finite-dimensional representation `X -> St_l(g) X rho(g)^(-1)` on
    `Hom(C^(l-1), C^l)`.  Its (T;FD) Kazhdan constant is inherited from the
    co-dense `SL_2(Z[1/p])`.
  - *Where every same-dimension repair dies.*  An invariant vector of that
    representation is an intertwiner.  Its image is an `St_l`-invariant
    subspace of dimension `<= l - 1 < l`, so it is `0`.  Hence the
    compression isometry `iota` is not almost invariant: its displacement is
    at least `kappa`, while exact repair within `delta` would make it at
    most `m(2/sqrt(l-1) + delta)`.
  - See `tfd-unbounded-irreps-group-is-not-strictly-hs-stable` (general
    (T;FD) theorem) and `sl2-z-inverse-pq-is-not-strictly-hs-stable`.
  - *What survives.*  The consumers
    `hnn-over-codense-kazhdan-subgroup-not-hyperlinear` and the HNN route
    only need flexible stability, which these tuples do not contradict: one
    extra dimension repairs them.  That hole is now
    `sl2-z-inverse-pq-is-flexibly-hs-stable`, with route
    `non-hyperlinear-from-hnn-over-sl2-pq-flexible-stability`.
  - *Same obstruction elsewhere.*  It applies verbatim to `SL_2(Z[1/p])` and
    to every (T;FD) group with unbounded finite-dimensional irreducibles.
    Every strict-reading stability hypothesis on such a group is false.
