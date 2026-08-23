---
rg: 2
id: km-group-ring-h2-vanishes-proof
kind: route
title: The cusp induction over levels with cohomology in degree four only
target: km-group-ring-h2-vanishes-for-the-lattices
requires:
  - km-thick-part-two-connected-and-lattice-is-f3
  - km-twisted-level-product-cycles-surject
  - km-group-ring-h2-is-development-end-cohomology
---

By `km-thick-part-two-connected-and-lattice-is-f3`,
`H^2(Lambda;Z Lambda) = H^2_c(X^) = H^3_c(Z minus X^)`.  Exhaust the
cusp region by the open sets `cusp_(<=R) = Z_(<=R) minus X^`, whose
successive quotient complexes are the level cochain complexes; by the
structure theorem and the established surjectivity, every level's
relative homology is free and concentrated in degree four, so by
universal coefficients `H^q(level R) = 0` for `q <= 3`.  The long
exact sequences of the pairs give `H^q_c(cusp_(<=R)) = 0` for
`q <= 3` by induction on `R` (base: the first level), and compactly
supported cohomology commutes with the increasing union, so
`H^3_c(Z minus X^) = 0`.  (`H^2_c(Z) = H^3_c(Z) = 0` by Künneth with
the degree-two concentration and freeness of the buildings' compactly
supported cohomology, circle nerve.)  The consistency of
`(GV1)` with `H^2(Lambda;Z Lambda) = H^1_infty(X)` of the
two-dimensional development is the statement that its point classes
pair nontrivially with the explicit 2-spheres: the development has
`H_2 != 0` and its compactly supported classes orthogonal to all
2-cycles all die, exactly as `(GV1)` requires.
