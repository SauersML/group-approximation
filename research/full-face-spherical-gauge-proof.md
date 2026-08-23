---
rg: 2
id: full-face-spherical-gauge-proof
kind: route
title: Compress every vertex word by the trivial central idempotent
target: full-km-face-kills-no-spherical-gauge
requires:
  - native-km-coset-coefficients-retain-spherical-pauli-absorber
  - kernel-section-builds-relative-p13-chart
---

The central idempotent `(FKF1)` projects the left regular representation to
its trivial subrepresentation.  Left multiplication by any group element
fixes the constant vector, proving `(FKF2)`.  A native kernel word `n_a` is a
product of elements of `P_1` and `P_3`, both contained in the adjacent
rank-two groups.  Applying `(FKF2)` factor by factor proves `(FKF3)` before
any estimate or limiting argument.

Every finite-label coefficient map is equivariant for the relevant
parabolic action.  Its compression between trivial summands is therefore a
scalar label map.  Amplification makes the compressed map that scalar
tensored with `I_m`; hence the actual face coefficient is independent of
the multiplicity gauge and has zero derivative there.

Finally, any unitary `W:C^m->C^m` is an exact intertwiner between two copies
of the trivial representation.  Replacing `W` by `I_m` cannot alter the
represented group matrices.  Choose the spherical overlap identifications
afresh, first as identities along a spanning tree and then as identities on
every chord.  This proves the zero-cost correction assertion and shows that
the Pauli chord previously inserted in the overlap coefficient system is a
choice of coordinates, not the compression of `pi(n_a)`.  Quotienting this
free choice gives `(FKF4)`; the already computed generalized-quadrangle
coefficient gives `(FKF5)` on its orthogonal complement.
