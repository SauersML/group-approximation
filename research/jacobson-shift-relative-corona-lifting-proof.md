---
rg: 2
id: jacobson-shift-relative-corona-lifting-proof
kind: route
title: Glue exact finite packets and correct one finite-group intertwiner before passing to the corona
target: jacobson-shift-gap-characterizes-mark-collapse
requires:
  - jacobson-stable-letter-closes-boundary-recursion
  - jacobson-full-boundary-packets-have-compatible-regular-models
  - jacobson-boundary-cell-reconstructs-finite-root-packet
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
  - research/artifacts/jacobson-boundary-packet-relative-rounding-2026-09-08.md
---

The regular `B` representation and the prescribed multiple of the
regular `C` representation glue on their full intersection. The
two restrictions of regular `B` to the equal-order copies `F`
and `alpha_F(F)` are equivalent, supplying an exact unitary
intertwiner. This proves nonemptiness while retaining the head.

For exact representations `rho_0,rho_1` of `F`, average
`rho_1(f)T rho_0(f)^*` over `F`. Its distance from `T` is
at most the maximum intertwining error. For error less than one,
the average is invertible and its unitary polar factor is an
exact intertwiner within twice that error. Conjugation of a
unitary changes by at most twice the change in `T`, giving the
claimed four-error bound.

The six specified involutions generate `F=G x G`. A simple path
in the Cayley graph of either 168-element factor has length at
most 167, so every element of `F` has word length at most 334.
Telescoping intertwining errors along such a word gives
`epsilon<=334 d_F`. This yields the stated bounds 668 and 1336.
For a nine-error tuple of maximum defect less than `1/334`, its
correction has objective at most 1337 times that defect. At larger
defect the global bound `gamma_shift<=2` gives the same inequality.
Taking infima, and noting that exact intertwiners have six zero
generator errors, proves both comparisons with `eta_shift`.

Zero infimum gives a sequence of exact finite-packet tuples and
exact intertwiners whose remaining relators vanish in the norm
corona. Their head involutions stay at norm distance two, giving
a marked homomorphism from `Theta_shift`.

Conversely lift a marked corona homomorphism to unitary matrices.
The finite-group correction theorem proved in the relative-rounding
artifact makes each of `B,C` exact in the original dimensions.
The polar factor of the finite averaged intertwiner on `Z` makes
their restrictions agree exactly. A second finite average, this
time over `F`, corrects the stable letter to an exact intertwiner.
All corrections tend to zero in norm, so the three mixed errors
still vanish. Infinitely many of the corrected head involutions
are nonidentity; restriction to those coordinates gives zero infimum.

No averaging over an infinite group or invariant-vector estimate for
an infinite subgroup is used. This establishes the equivalence,
not the missing positive lower bound.
