---
rg: 2
id: km-thick-part-two-connected-via-twisted-surjectivity
kind: route
title: Run the codistance filtration with vanishing twisted cokernels
target: km-thick-part-two-connected-and-lattice-is-f3
requires:
  - km-twisted-level-product-cycles-surject
  - km-codistance-filtration-twisted-levels-are-rank-two-pairs
---

By the structure theorem every level `Z_(<=R+1)/Z_(<=R)` has relative
homology concentrated in degree four except at twisted rank-two levels,
where `H_1 = H_2 = 0` always and `H_3` is the cokernel of `(TLS1)`.  Under
the open input that cokernel vanishes, so the maps
`H_k(Z_(<=R)) -> H_k(Z_(<=R+1))` are isomorphisms for `k <= 2` and all
`R >= 0`; taking the limit, `H_k(X^) = H_k(Z) = 0` for `k = 1, 2`.  `X^` is
simply connected (van Kampen over a regular neighbourhood of the
mixed-type 1-skeleton: its complement is homotopy equivalent to the
simply connected development, and all links of mixed cells are
connected), hence 2-connected by Hurewicz.  Brown's criterion with
finite stabilizers and finitely many orbits of cells gives type `F_3`.
Universal coefficients with `H_1(X^)=H_2(X^)=0` make
`H^2(X^; Z Lambda)=0`, so the inflation
`H^2(Lambda;Z Lambda) -> H^2_Lambda(X^;Z Lambda) = H^2_c(X^)` of
`triangle-colimit-rational-h2-vanishes` (RH2) is an isomorphism.
