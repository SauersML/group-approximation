---
rg: 2
id: stw99-lxxvi-pure-dimension-drop-scalar-kernel-proof
kind: route
title: Obtain prime dimension-drop maps from unit divisibility and kill scalar kernels in stable endpoint range
target: stw99-lxxvi-pure-coefficients-kill-scalar-unstable-homotopy
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-scalar-unstable-homotopy-audit-2026-09-05.md
---

Since `[1_A]` is compact, almost divisibility gives
`n x<=[1_A]<=(n+1)x` in Cu. Approximate `x` from below by finite-matrix
classes and use compactness of the unit to retain the second inequality.
This gives the same inequalities for some `y in W(A)`.
Rørdam--Winter, arXiv:0801.2259v1 Proposition 5.1, then gives a unital
*-homomorphism `Z_(n,n+1)->A` when `A` has stable rank one.

Fix `r,k` and choose `n` with `k+1<2rn`. The unitary group of
`M_r(Z_(n,n+1))` is the homotopy pullback of endpoint groups
`U(rn),U(r(n+1))` over `U(rn(n+1))`. In degree `k+1`, all three groups
are in the classical stable range, and the difference map is
`(x,y) |-> (n+1)x-n y` on the stable homotopy group. It is surjective
because `n,n+1` are coprime. Exactness therefore makes endpoint
evaluation injective on degree `k` of the pullback.

A scalar stably trivial `alpha in pi_k(U(r))` has zero image in both
stable endpoint groups. Hence its image in the pullback is zero, and
the unital map into `A` kills its scalar-extension image there too.

Lin's simple-pure dichotomy handles the finite simple case. In the
purely infinite simple case the unitary homotopy stabilization maps
are already isomorphisms by the known K-stability theorem, so scalar
stable-zero classes also vanish. Clutching gives the asserted
isomorphism of the scalar-extended sphere bundles.
