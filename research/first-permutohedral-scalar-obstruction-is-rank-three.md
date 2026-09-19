---
rg: 2
id: first-permutohedral-scalar-obstruction-is-rank-three
kind: claim
title: The first scalar compatibility obstruction is a closed rank-three permutohedral surface
distinct_from:
  isolated-regular-a2-hexagon-has-free-external-holonomy: that proves full external unitary freedom on one cell; this identifies the first incidence pattern on which even the scalar determinant of those gauges can become gauge-invariant.
  braid-prefix-label-space-has-no-ucp-expectation: that finds a positivity obstruction for repeated label averaging already on a path and a hexagon; this is a cohomological statement about edge compatibility gauges, not about a ucp projection onto a label space.
  steinberg-group-is-glued-over-the-permutohedron: that localizes the presentation to square and hexagonal cells; this distinguishes contractible single-cell data from the first closed two-cycle among those cells.
---

**ESTABLISHED SCOPED INCIDENCE FENCE.**  Consider only the central scalar
part of packet compatibility gauges.  Give every oriented edge `e` of a
finite two-complex a phase `z_e in U(1)`, with `z_(bar e)=z_e^(-1)`.  The
phase inserted around an oriented face `f` is

```text
(delta z)_f=product_(e in boundary f) z_e^(epsilon_(f,e)). (PSC1)
```

1. On one braid hexagon, every prescribed face phase can be cancelled by
   changing one boundary-edge phase.
2. The same is true on two hexagons sharing one edge, and more generally on
   every face complex which can be removed one face at a time along a free
   edge.  Shared cells are therefore necessary but **not sufficient** for a
   scalar compatibility obstruction.
3. On a closed oriented surface the product of all oriented face phases is
   unchanged by every edge correction, because each edge occurs twice with
   opposite signs.  Hence

```text
product_f c_f=1                                           (PSC2)
```

   is necessary for prescribed scalar curvatures `c_f` to be gauged flat.

For the Coxeter-permutohedral atlas, the rank-two `S_3` piece is a single
hexagonal disk and has no such obstruction.  The first closed two-cycle is
the boundary of the rank-three `S_4` permutohedron (the truncated
octahedron), consisting of eight braid hexagons and six commuting squares.
If the square phases are already authenticated as `1`, the first possible
scalar obstruction is therefore

```text
product_(eight braid faces) c_f != 1.                    (PSC3)
```

This does **not** prove that `(PSC3)` occurs in a binary-Leavitt microstate.
The regular finite-Chevalley packet has every `c_f=1`.  To use `(PSC3)` for
`leavitt-regular-character-is-not-mf`, one must still extract the face
phases from literal shared group-word occurrences and prove that their
product is nontrivial with a dimension-independent operator-norm modulus.
The statement only identifies the smallest genuine compatibility target and
rules out a single braid hexagon (or a disk of shared hexagons) as that
target.

There is a further decisive limitation.  By
`permutohedral-determinant-flux-is-bianchi-trivial`, if the `c_f` are the
determinant curvatures of one genuinely shared edge family, `(PSC2)` holds
identically.  Thus the rank-three sphere is the first **incidence equation**
for independently prescribed face targets, but it cannot itself provide a
nonzero determinant obstruction.  A genuine obstruction there must retain
nonabelian, occurrence-typed packet data.

DERIVATION
first-permutohedral-scalar-obstruction-proof
