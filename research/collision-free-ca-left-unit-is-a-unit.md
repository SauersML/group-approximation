---
rg: 2
id: collision-free-ca-left-unit-is-a-unit
kind: claim
title: A cellular-automaton left unit on a collision-free memory rectangle is already a unit
artifacts:
  - research/artifacts/gottschalk-nonlinear-ca-search-2026-08-24.md
  - research/artifacts/gottschalk-nonlinear-ca-search-2026-08-24.py
---

Let `A` be a nonempty finite alphabet and `G` a group.  Let
`tau, sigma : A^G -> A^G` be cellular automata with finite memory sets `S,T`
and local rules `mu : A^S -> A`, `nu : A^T -> A`.  Suppose

    sigma . tau = id.

If the multiplication map

    T x S -> G,    (t,s) |-> t s

is injective, then `tau` is bijective.  More precisely, there is a unique pair
`(t0,s0)` with `t0 s0 = 1`, and `mu` depends only on the coordinate `s0`, by a
permutation of `A`.  Thus `tau` is an invertible coordinate shift followed by
an alphabet permutation.

Consequently a strict full-shift embedding can only occur when its encoder and
a finite-memory left inverse have a genuine multiplication collision

    t s = t' s'    with (t,s) != (t',s').

This is an unconditional finite-memory obstruction; it uses neither soficity
nor amenability nor any Leavitt structure.
