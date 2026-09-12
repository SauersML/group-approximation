---
rg: 2
id: stw59-trace-contraction-and-stiefel-stable-range-proof
kind: route
title: Equal-rank evaluation halves contract traces and amplified bundles enter every fixed homotopy stable range
target: stw59-monotracial-matrix-stable-counterexamples
requires:
  - stw59-exact-finite-abelian-unitary-component-groups
artifacts:
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
---

The normalized fiber trace of phi_i(a) is one half the pullback of
the old normalized fiber trace plus one half its value at x_i.
Iterating contracts the difference of any two limit traces to zero.
Existence was established in the original tower. At each connected
base, virtual bundle rank gives precisely the trace image (1/r_i) Z;
K0 continuity gives their dyadic union.

For a rank-r bundle F on a d-dimensional finite CW base, the space
of embeddings H into F plus H has Stiefel fiber U(r+s)/U(r), which
is 2r-connected. Its section space is (2r-d)-connected. Explicit
polar lifts make the gauge map a locally trivial principal bundle.
The homotopy exact sequence therefore makes stabilization an
isomorphism on pi_k when d+k+1<=2r. Taking H=F gives the actual
matrix maps and their canonical stable K-theory identification.

In M_m(A_i), this inequality is k+1<=2(m-1)r_i. It holds on a
tail for every fixed m>=2 and k. Compact sphere approximation and
relative disk approximation prove homotopy-group continuity, while
K-theory continuity and naturality pass the canonical isomorphism
to the limit. The full corner diag(1,0) in M2(A_G) is A_G itself.

Nistor's Theorem 7(a) gives stable rank two for each locally trivial
homogeneous stage of dimension twice its matrix degree. Density of
generating pairs passes to the limit. The nonzero size-one kernel
excludes stable rank one by Rieffel, so the limit has stable rank two.
