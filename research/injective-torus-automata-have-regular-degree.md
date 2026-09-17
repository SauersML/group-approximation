---
rg: 2
id: injective-torus-automata-have-regular-degree
kind: claim
title: Over every group, an injective continuous equivariant self-map of a torus full shift has a degree matrix that is regular over Q[G]
distinct_from:
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that proves this regularity in two cases, residually finite groups and the circle alphabet over domain group rings; this is the statement for every group and every torus dimension.
  gottschalk-surjunctivity-conjecture: the dead co-Hopfian lease on that node used homology of pattern permutation modules of finite shifts, where every automaton acts as the identity; here the alphabet is connected, first cohomology is the free module Z[G]^d, and automata act by a nontrivial degree matrix.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

For every countable group `G`, every `d >= 1`, and every injective continuous
`G`-equivariant `tau: (T^d)^G -> (T^d)^G`, right multiplication by the degree matrix
`D(tau)` is injective on `Q[G]^d`.

Together with `torus-automata-with-regular-degree-are-surjective` this gives
`every-group-is-torus-surjunctive`. The statement is a topological invariance-of-domain
principle for `G`-full shifts over tori. It involves no finite alphabet, so it can fail
independently of Gottschalk's conjecture.

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): artifact Section 3.1.
  - **Known cases.**
    - Residually finite `G`, all `d`.
    - `Q[G]` a domain, `d = 1`.
    - Both come from invariance of domain on periodic tori.
  - **Obstruction to the constants-only argument.**
    - *What the constants give.* Only `epsilon(D) in GL_d(Z)`.
    - *Why that is not enough.* In `Z[Z/2 x Z/3]`, `D = s + s^2 - t` has
      `epsilon(D) = 1` and kills `(1-t)(1-s)`. So over a non-residually-finite host with
      torsion, or with `d >= 2`, a proof must see beyond finite-dimensional invariant
      submanifolds.
    - *What would replace them.* An infinite-dimensional invariance of domain: a strict
      decrease of a mean-dimension-type invariant on proper subsystems. That is sofic
      mean dimension over sofic groups, and nothing is known beyond them.
  - **How a counterexample would look.** An injective torus automaton with a singular
    degree matrix. Every character `x -> <gxi, x>` with `xi D = 0` pulls back to a
    nullhomotopic function on the image. So the image is an equivariant copy of the full
    torus shift on which a whole `G`-module of characters is homotopically trivial.
