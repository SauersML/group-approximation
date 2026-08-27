---
rg: 2
id: leavitt-three-gate-square-picture-area-eight-proof
kind: route
title: Reduce area six to sixteen cubic planar multigraphs and sixteen relator-colour orbits
target: leavitt-three-gate-square-picture-area-eight
requires:
  - leavitt-three-gate-kernel-picture-has-area-at-least-six
---

A six-vertex relative picture has nine `z`-arcs.  On the sphere its ribbon
dual is a connected cubic planar multigraph with five coefficient regions.
Sign balance forces three positively and three negatively oriented relator
vertices.  After fixing that split, the artifact first enumerates the planar
ribbon pairings without assigning `R_0/R_1` colours.

Up to permutation of the six vertices, their underlying cubic multigraphs
fall into sixteen types.  The unique simple type is the triangular prism
(`K_(3,3)` is nonplanar); the remaining fifteen have loops or parallel edges,
including the theta and `K_4`-derived degenerations.  Thus the search is over
the complete low-curvature graph list, not over arbitrary relator words.

The residual `S_3 x S_3` symmetry says that an `R_0/R_1` colouring is
determined, up to relabelling already present in the ribbon enumeration, by
the number of `R_1` vertices in each orientation class.  There are only
`4*4=16` such colour types.  For every type the artifact:

1. removes any arc joining occurrence `i` of `R_j` to inverse occurrence
   `2-i` of `R_j^(-1)`, an immediate dipole;
2. computes the five ribbon-region cycles;
3. reduces their labels in
   `C_2(h_0)*Z(h_1)*C_2(h_2)*C_2(k_0)*Z(k_1)*Z(k_2)`;
4. permits any one region to be the outer coefficient boundary and requires
   the other four to be trivial.

There are `596856` dipole-free planar coloured ribbon pairings after these
symmetry reductions and no candidate disk.  Since picture area is even, the
universal-square lower bound rises from six to eight.

The obstruction is structural.  The prism and every parallel-edge
degeneration force at least one internal region to contain one of the
non-gate labels `h_1,k_1,k_2` (or a noncancelling mixture) after all square
regions are removed.  Therefore an actual Leavitt picture with at most six
cells can close only by a new identity among

```text
h_1=q_0p_1,       k_1=q_1,       k_2=p_0e_1
```

together with the gate labels.  This identifies the next computation: test
the finite set of non-gate region words produced by the sixteen graph types
in the faithful infinite-word model.  Pure repetition of the three torsion
folds cannot yield a kernel before area eight.
