---
rg: 2
id: stw58-free-diffuse-exponential-and-existential-reflection-proof
kind: route
title: Smooth a sphere family by a based free exponential and reflect its finite-data contraction
target: stw58-tracial-selfless-k-stability
requires:
  - stw58-fixed-spectral-point-small-support-localization
  - stw58-simple-finite-pure-split-stable-surjectivity
artifacts:
  - research/artifacts/stw58-tracial-selfless-k-stability-free-smoothing-2026-09-05.md
---

1. Robert's Theorems 2.6(iv), 4.2, and 3.1(ii) give an existential
   inclusion \(B\to D=B*C(\mathbb T)\), with \(D\) again selfless,
   simple, stably finite, and possessing exactly one normalized
   2-quasitrace, the free product trace. Gould's Corollary 3 gives
   purity.
2. For the free Haar generator \(w\), the positive contraction
   \(a=(1+\operatorname{Re}w)/2\) has atomless distribution.
   Choose continuous \(t:S^k\to[0,1]\) vanishing exactly at the
   basepoint. The formula
   \(U_s(x)=u(x)\exp(i s t(x)a)\) is an actual based homotopy.
3. Off the basepoint, the exponential is diffuse and free from
   \(u(x)\). Belinschi--Bercovici--Ho Lemma 3.1(1) makes the
   product distribution atomless; a scalar first factor simply
   rotates the diffuse measure. At the basepoint the distribution
   is \(\delta_1\), so there is no atom at the fixed point \(-1\)
   anywhere.
4. Fixed spectral-point localization and small-support contraction
   make every stably null image family contract in \(U(D)\).
   Compactness supplies a uniform arc even as \(t(x)\) tends to
   zero at the basepoint.
5. Existentiality reflects the completed contraction to \(B\).
   Triangulate a unitary null-disk, use only finitely many unit-ball
   variables with approximate unitary and edge-distance conditions,
   and reflect those conditions. Polar vertex correction and
   barycentric polar interpolation construct a disk in \(U(B)\);
   a short boundary collar restores the exact original family.
   The artifact supplies explicit bounds and based normalization.
6. This proves injectivity in every positive degree. The required
   reviewed theorem supplies surjectivity, and stable rank one
   supplies degree-zero bijectivity. Robert's matrix-selflessness
   theorem applies the same proof at every matrix size. Naturality
   of canonical stabilization proves that consecutive maps are
   isomorphisms.

This route uses a genuine homotopy followed by reflection of its
finite data. Equality of stable K-classes alone is never used as a
substitute for that homotopy. Exact primary-source statements and
their hypotheses are checked in the internally reviewed artifact.
