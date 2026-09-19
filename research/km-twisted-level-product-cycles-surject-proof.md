---
rg: 2
id: km-twisted-level-product-cycles-surject-proof
kind: route
title: Disjoint-class single-slot construction over the threshold law
target: km-twisted-level-product-cycles-surject
requires:
  - km-codistance-filtration-twisted-levels-are-rank-two-pairs
  - km-opposition-class-walk-threshold-law
---

For the lattices of the program the parameter satisfies `q > 1764^3`,
far above every threshold below; the statement is proved for
`q + 1 >= 2d + 1` at each level type (`d` the Frattini dimension:
grid levels hold for all `q` by the star computation recorded in the
target's attempts, `B_2` levels for `q >= 6`, hexagon levels for
`q >= 8`), in every characteristic.

Fix a twisted level, a class `i`, base points `p'_0` (A side) and
`p''_0` (B side) of class `i`, integral targets `a in Z_0(N p'_0)` and
`b in Z_0(N p''_0)`, and disjoint class sets `C, C'` avoiding `i` with
`|C| = |C'| = d`.

1. By the threshold law the `C`-walk graph is connected and contains
   every opposite line, and likewise for `C'` on the `B` side.
2. For an elementary difference `e_l - e_(l')` at `p'_0`: take a path
   between the lines `l` and `l'` in the `C`-walk graph; its interior
   vertices are lines and class-`C` points, so it never meets `p'_0`
   or any other class-`i` point; closing it through `p'_0` yields an
   integral cycle whose local datum is `e_l - e_(l')` at `p'_0` and
   zero at every other class-`i` point, with point-support otherwise
   in classes `C`.  Sums realize any `a`; similarly any `b` on the `B`
   side with class support in `C'`.
3. The image of the product of these cycles has a nonzero entry only
   at matched-class slots whose class lies in
   `({i} cup C) cap ({i} cup C') = {i}`, where each factor's only
   class-`i` point is its base point: the image is `a (x) b` at
   `(p'_0, p''_0)` and zero at every other slot.  Single slots
   generate the target over `Z`, so the map is integrally surjective.

Verification record: the threshold law and every combinatorial premise
are computationally verified (hexagon `q = 2..5`, quadrangle
`q = 3, 4`, grid rank check; artifact
km-opposition-connectivity-computations-2026-08-23.md), the level
formula is confirmed by two-path homology computations in both
regimes, and the double-coset and wall-geometry inputs of the
structure theorem pass direct Coxeter enumeration
(experiments/km_coxeter_descent_checks.py).  An external adversarial
audit of the analytic steps was still running when this route was
landed; its report should be checked against this chain.
