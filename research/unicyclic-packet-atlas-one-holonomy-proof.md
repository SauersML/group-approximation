---
rg: 2
id: unicyclic-packet-atlas-one-holonomy-proof
kind: route
title: Transport along a spanning tree and read the chord freedom as one commutant coset
target: unicyclic-packet-atlas-concentrates-incidence-in-one-holonomy
requires: []
---

The argument is the one written in the claim body; this route records it
as a proof with the two facts it uses made explicit.

**Fact A (amplified equivalence).**  Two unitary representations of a
finite group with the same set of irreducible constituents and every
retained multiplicity countably infinite are unitarily equivalent: each
is the direct sum over that common support of `aleph_0` copies of each
constituent, and a bijection of copies is an intertwining unitary.
Countable amplification (tensoring every vertex representation with
`l^2(N)`) makes every retained multiplicity countably infinite and does not
change the irreducible support of any restriction.

**Fact B (intertwiner torsor).**  If `u` is a unitary intertwiner from a
representation `sigma` to a representation `sigma'`, then the unitary
intertwiners from `sigma` to `sigma'` are exactly `u h` with `h` a unitary
in the commutant `sigma(H)'`: `u h` intertwines iff `h` commutes with
`sigma(H)`, and `u^(-1) u'` is such an `h` for any other intertwiner `u'`.

**Tree step.**  Fix a spanning tree `T` of the graph and a root.  Process
the vertices in breadth-first order from the root.  For a tree edge
`e = (v, w)` with `v` already processed and `w` its child, the two
restrictions `pi_v|_(H_e)` and `pi_w|_(H_e)` have the same irreducible
support by hypothesis, hence (Fact A, after amplification) a unitary
intertwiner `u_e : pi_w|_(H_e) -> pi_v|_(H_e)`; replace `pi_w` by the
conjugate `u_e pi_w u_e^(-1)`.  Conjugating `pi_w` globally changes all of
its edge restrictions by the same unitary, so the edge `e` now has literally
equal endpoint restrictions, and no previously processed edge is affected
because each vertex is conjugated exactly once, when it is first reached.
Since `T` has no cycles, every tree edge is made exact and the choices on
distinct tree edges are independent.

**Chord step.**  The first Betti number is one, so exactly one edge
`e = (v, w)` is not in `T`.  After the tree step, `pi_v|_(H_e)` and
`pi_w|_(H_e)` still have the same irreducible support with infinite
multiplicities, so a unitary intertwiner `u_e` exists (Fact A), and by Fact
B every exact choice on the chord is `u_e h` with `h in pi_e(H_e)'`, which
is `(UPA1)`.  Conversely, any `h` in that commutant gives an exact incidence
on `e`, and the tree incidences are untouched by it, so the set of exact
completions of the whole atlas is the single torsor `u_e . U(pi_e(H_e)')`
of the chord separator; this is `(UPA2)`.  Nothing finite-dimensional is
asserted: the statement is about exact completeness after amplification
only, as the claim says.
