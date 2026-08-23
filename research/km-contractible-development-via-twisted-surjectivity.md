---
rg: 2
id: km-contractible-development-via-twisted-surjectivity
kind: route
title: Contractible development from the twisted-level surjectivity, then the point class
target: km-development-has-nonzero-end-cohomology-in-degree-one
requires:
  - km-twisted-level-product-cycles-surject
  - km-codistance-filtration-twisted-levels-are-rank-two-pairs
  - km-group-ring-h2-is-development-end-cohomology
---

By the structure theorem every level of the codistance filtration has
relative homology concentrated in degree four except the twisted
rank-two levels, whose only possible lower relative homology is
`H_3 = H~_2(Omega)`, the cokernel in `(TLS1)`.  Under the open input
that cokernel vanishes, so `H_k(Z_(<=R))` is independent of `R` for
`k<=2` and equals `H_k(Z)=0`: `H_2(X)=0`.  The development is simply
connected, so it is contractible.  Then every 2-cycle of `X` is zero,
the point class of a single 2-cell is a nonzero element of `H^2_c(X;Z)`
(its total mass on its twin-apartment plane is one), and it lies in
`ker(H^2_c(X) -> H^2(X)) = H^1_infty(X)` for trivial reasons; this is
the target by `km-group-ring-h2-is-development-end-cohomology`.
