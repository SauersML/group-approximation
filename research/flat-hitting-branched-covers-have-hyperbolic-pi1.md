---
rg: 2
id: flat-hitting-branched-covers-have-hyperbolic-pi1
kind: claim
title: A branched cover whose branch links have girth above 2pi and whose branch set meets every flat R-disk has hyperbolic fundamental group
distinct_from:
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that transfers soficity from the cover's fundamental group to the base; this gives a checkable geometric condition making that fundamental group hyperbolic.
  hyperbolic-cubulated-groups-are-residually-finite: that imports Agol's theorem for hyperbolic cubulated groups; this produces hyperbolic groups, which in the square-complex case feed that import.
---

**ESTABLISHED** (proof: `flat-hitting-branched-covers-hyperbolic-proof`).

Let `Y` and `p: X -> Y` be a locally CAT(0) piecewise Euclidean 2-complex and
a finite branched cover, as in `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`,
with branch set `B`.  Suppose:

* **(G) branch girth.**  For every `b in B`, the angular girth of `Lk(b)` is
  strictly greater than `2 pi`.  For the Titz Mite--Witzel complex `Y_1^2`
  this means combinatorial girth at least 10 at branch vertices of
  generalized-quadrangle type (edge angle `pi/4`), and at least 6 at branch
  vertices of `K_(3,3)` type (edge angle `pi/2`).  For a square complex with
  `K_(m,n)` links it means combinatorial girth at least 6.
* **(H) flat hitting.**  For some `R`, there is no locally isometric
  immersion of the closed Euclidean disk of radius `R` into `X \ B`.

Then `X~` contains no isometrically embedded Euclidean plane.  So
`Lambda = pi_1(X)` is a torsion-free hyperbolic group acting freely and
cocompactly on the CAT(0) complex `X~`.  If `Y` is a square complex, `X~`
is a 2-dimensional CAT(0) cube complex, so `Lambda` is cubulated hyperbolic,
hence virtually special and residually finite
(`hyperbolic-cubulated-groups-are-residually-finite`).

Condition (H) is a finite check for a given `X`.  Every locally isometric
immersion of a disk into `X \ B` develops isometrically into `Delta = Y~`
(Lemma 1 of `sparse-branched-covers-sofic-pi1-reduction-proof`).  Every
2-flat of a piecewise Euclidean 2-complex is a union of closed 2-cells.  So
(H) asks that every combinatorial flat `R`-disk of `Delta`, lifted to `X`
from any vertex over its centre, runs into `B`.

DERIVATION
flat-hitting-branched-covers-hyperbolic-proof
