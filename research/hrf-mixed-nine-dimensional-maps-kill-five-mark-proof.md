---
rg: 2
id: hrf-mixed-nine-dimensional-maps-kill-five-mark-proof
kind: route
title: Use the nine-character root orbit and split off central eigenspaces, treating characteristic five by Schur's lemma
target: hrf-mixed-nine-dimensional-maps-kill-five-mark
requires:
  - hrf-mixed-detectors-have-balanced-edge-spectra
  - hrf-amplified-sym4-five-twists-have-no-detectors
artifacts:
  - research/artifacts/hrf-mixed-nine-dimensional-obstruction-2026-09-20.md
---

Extend the field to an algebraic closure. In `S=PSL_2(F_19)`,
upper and lower elementary matrices generate. With
`h=diag(2,2^-1)`, conjugation sends `u(t)` to `u(4t)` and
`h u(t)h^-1u(t)^-1=u(3t)`. Hence every upper elementary
matrix is a commutator; the lower ones are conjugate to these,
so `S` is perfect.

If the characteristic is not nineteen, the upper root subgroup
`U=C_19` acts semisimply. If it acts trivially, its conjugate lower
subgroup does too, so all of `S` acts trivially. Otherwise a
nontrivial `U` character occurs. The normalizing torus permutes
nontrivial characters by the order-nine exponent multiplier four.
Their orbits have length nine; their eigenspaces have equal positive
dimension. Every nontrivial `S`-module consequently has dimension
at least nine in these characteristics.

Suppose first the characteristic is not five and the mark survives.
A nontrivial central eigenspace is invariant under the whole triangle.
The spectral dependency makes its dimension a positive multiple
of five, hence exactly five. Outside characteristic nineteen, the
preceding bound makes all vertex actions there trivial, contradicting
any nonzero twisted edge. In characteristic nineteen, the balance
equations force the sole composition factor at each vertex to be
`L4=Sym^4`. The amplified dependency at multiplicity one excludes
this case as well.

In characteristic five, any nontrivial vertex module has a nontrivial
simple composition factor: otherwise its image is unitriangular and
solvable, whereas it is also perfect, hence trivial. Such a factor
has dimension at least nine by the root-orbit argument. Thus any
nontrivial vertex action in total dimension at most nine is itself
irreducible of dimension nine. Its commuting central mark is scalar
by Schur's lemma and equals one because the only fifth root of one
in characteristic five is one. If all vertices act trivially, a
nonzero edge relation and `Z^5=1` kill the mark directly. This proves
the claim in every characteristic, and field extension descends
the identity to the original field.

The artifact supplies all conventions, the faithful natural linear
and unitary corollaries, and the explicit boundary at abstract
projective quotient statements. The root lane supplied this argument;
the child lane independently checked it. No computation is used.
