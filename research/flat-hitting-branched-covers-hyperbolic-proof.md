---
rg: 2
id: flat-hitting-branched-covers-hyperbolic-proof
kind: route
title: A flat through a branch vertex needs a 2pi cycle in its link; a flat avoiding branch vertices immerses every disk
target: flat-hitting-branched-covers-have-hyperbolic-pi1
requires:
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - hyperbolic-cubulated-groups-are-residually-finite
---

Imports: Bridson--Haefliger I.7.39 (for finitely many shapes, a small ball
about a point `x` is isometric to the ball about the cone point of the
Euclidean cone on `Lk(x)`); the flat plane theorem III.H.1.5 (a proper
cocompact CAT(0) space is hyperbolic iff it contains no isometric copy of
`E^2`); and Švarc--Milnor I.8.19.

By part 3 of the prerequisite, `X~` is CAT(0), and `Lambda` acts on it
freely, properly and cocompactly.  Suppose `P subset X~` is an isometrically
embedded plane.

**No branch vertex on `P`.**  Let `b~ in P` lie over `b in B`.  For small
`epsilon` the disk `P cap B(b~, epsilon)` sits in the Euclidean cone on
`Lk(b)`.  Its radii are geodesics from the cone point, hence radial:
`t -> t xi(theta)`.  In the cone,

```text
d(t xi, t eta)^2 = 2 t^2 (1 - cos min(pi, d_Lk(xi,eta))) ,
```

while in `P` the same distance is `2 t^2 (1 - cos(theta - theta'))`.  Hence
`d_Lk(xi(theta), xi(theta')) = |theta - theta'|` whenever
`|theta - theta'| <= pi`.

So `theta -> xi(theta)` is a closed local geodesic of length `2 pi` in the
metric graph `Lk(b)`.  That is a closed path without backtracking, and it
contains an embedded cycle of length at most `2 pi`.  This contradicts (G).

**`P` immerses every disk.**  So `P cap B~ = empty`.  Composing an isometric
disk of radius `R` in `P` with the covering `X~ -> X` gives a locally
isometric immersion into `X \ B`, contradicting (H).

Therefore `X~` contains no flat, so it is hyperbolic (III.H.1.5), and
`Lambda` is quasi-isometric to it (I.8.19), hence hyperbolic.  It is
torsion-free because it acts freely on a CAT(0) space: a finite group has a
fixed point.

**Square case.**  A piecewise Euclidean complex built from unit squares,
whose links have girth at least 4, is a nonpositively curved square
complex.  Its universal cover is a CAT(0) cube complex, and the action of
`Lambda` is proper and cocompact.  So `hyperbolic-cubulated-groups-are-residually-finite`
applies.

**Flats are subcomplexes (for the remark on checking (H)).**  If a flat meets
an open 2-cell, then near that point both are 2-manifolds.  By invariance of
domain the flat contains a neighbourhood, so it contains the whole open cell
by connectedness.  A flat has empty interior relative to the 1-skeleton, so
it is the closure of the open 2-cells it meets.
