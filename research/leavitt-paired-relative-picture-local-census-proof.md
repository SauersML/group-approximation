---
rg: 2
id: leavitt-paired-relative-picture-local-census-proof
kind: route
title: Reduce corner words in the free product and enumerate the symmetrized hexagon overlaps
target: leavitt-paired-relative-picture-local-census
requires:
  - leavitt-length-six-full-support-torsion-candidate
---

## Coefficient regions

Expand each `h_i,k_i` into its alternating `G_0,G_1` syllables.  A product is
the identity in `H=G_0*G_1` only if free-product reduction erases every
same-copy block.  The artifact enumerates all cyclically formally reduced
products of one through four oriented corner labels.

For every block asserted nontrivial, it supplies a moved basis vector in the
standard faithful representation of the binary Leavitt algebra on infinite
binary words.  The words used by the computation are represented exactly as
eventually constant sequences `(finite prefix)(tail)^infinity`; there is no
finite-prefix approximation.  The coordinate cycle `p` is evaluated as an
actual permutation of twenty coordinates.  Hence each reported witness is
an exact certificate of nonidentity in `GL_20(R)`.

The census gives:

* degree one: no relation;
* degree two: only the four oriented versions of `h_2h_2` and `k_0k_0`;
* degree three: no relation;
* degree four: every relation has, after a cyclic rotation, the form
  `u u v v`, with `u,v in {h_2^(+-1),k_0^(+-1)}` and the two equal names at
  each adjacent pair.

The positive identities in the last two items are algebraic, not empirical:
`h_2=e_0=x_12(t_1)` and `k_0=a_1=x_12(s_0)`, and every elementary root has
order two in characteristic two.  Thus all degree-four identities are
products of the two square gates.

## Symmetrized overlaps

At alternating `H,<z>` syllable level, form all cyclic conjugates of
`R_0^(+-1)` and `R_1^(+-1)`.  Treat coefficient inverses formally except for
the two proved identities `h_2^(-1)=h_2` and `k_0^(-1)=k_0`.  Direct comparison
gives only single `z^(+-1)` overlaps, with four exceptions:

```text
h_2 z^(-1),       z h_2 z^(-1),
k_0 z,            z^(-1) k_0 z.
```

The length-two exceptions are subwords of the displayed length-three ones.
They occur between a relator and an inverse cyclic conjugate of the same
relator.  Since

```text
(z h_2 z^(-1))^2=1,       (z^(-1) k_0 z)^2=1,
```

these are genuine torsion self-overlaps, not artifacts of notation.  In
particular the usual relative `C(6)` curvature argument cannot be invoked:
a symmetrized relator has relative length six but contains a piece of length
three.

This is a local census only.  It neither constructs a spherical picture nor
proves coefficient injectivity.  Its exact consequence is the reduction of
the remaining diagrammatic problem to global chains alternating the two
torsion gates; any claimed Freiheitssatz must rule out those chains, and any
claimed kernel element must use them.

