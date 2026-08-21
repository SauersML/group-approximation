---
rg: 2
id: sl2-z-inverse-pq-is-hs-stable
kind: claim
title: SL2(Z[1/pq]) is Hilbert--Schmidt stable
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that consumes stability of a lattice such as SL2(Z[1/p]) through a central extension; this asks for stability of the three-place lattice SL2(Z[1/pq]), consumed through the Pauli lamplighter over its subgroup SL2(Z[1/p]) with no central extension.
---

Show that `SL_2(Z[1/pq])` (`p != q` primes) is HS-stable in the
same-dimension sense: for every `eps > 0` there is `delta > 0` such that
every finite-dimensional unitary tuple with relator defect below `delta`
is within `eps` (normalized HS, on generators) of an exact unitary
representation.

By `sl2-s-arithmetic-pair-is-codense-kazhdan` and
`pauli-lamplighter-over-stable-codense-kazhdan-pair`, this makes the
finitely presented Pauli lamplighter `Gamma_(p,q)` of `(SA1)` an explicit
nonhyperlinear group.

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
