---
rg: 2
id: stw58-uniform-spectral-arc-and-degree-one-squeezing-proof
kind: route
title: Use quasitrace compactness to choose one spectral arc and a normalized degree-one squeezing map
target: stw58-fixed-spectral-point-small-support-localization
requires:
  - stw58-small-quasitrace-support-kernel-vanishing
  - stw58-canonical-small-support-stable-splitting
artifacts:
  - research/artifacts/stw58-fixed-spectral-point-global-localization-2026-09-05.md
---

1. Continuous scalar functional calculus and the normalized quasitrace
   Lipschitz bound make \((x,\tau)\mapsto\tau(g(u(x)))\) jointly
   continuous. Decreasing positive peaks at \(\lambda\) show its
   atom-mass function is upper semicontinuous on the compact space
   \(X\times QT_1(B)\).
2. The strict pointwise atom bound therefore has a uniform margin.
   A finite subcover of the increasing sets where the peak integrals
   fall below an intermediate threshold gives one proper arc \(J\),
   disjoint from \(1\), with uniformly small spectral mass.
3. Choose a degree-one circle function \(f\), equal to one outside
   \(J\). The ratio \(z/f(z)\) has degree zero and equals one at \(1\),
   so it has a real continuous logarithm \(L\) with \(L(1)=0\).
4. Functional calculus gives the exact factorization
   \(u=f(u)\exp(iL(u))\) and its based homotopy to \(f(u)\).
   The displacement support of \(f(u)\) has dimension at most the
   spectral mass of \(J\).
5. Apply small-support contraction when the stable class is zero.
   For spheres of arbitrary stable class, compare to an arbitrarily
   small representative of the canonical lift; their combined
   support is below the contraction threshold, proving membership
   in the canonical stable summand.

Blackadar--Handelman's compactness and Lipschitz inputs and the
elementary covering-space logarithm are stated precisely in the
internally reviewed artifact. No moving spectral cut is selected.
