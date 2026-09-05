---
rg: 2
id: stw58-projection-copies-and-skeletal-stable-rank-proof
kind: route
title: Construct orthogonal projection copies and contract in a corner with controlled stable rank
target: stw58-small-projection-support-kernel-vanishing
requires: []
artifacts:
  - research/artifacts/stw58-small-projection-support-kernel-contraction-2026-09-05.md
---

1. The varying projection corner \(D=pC(X,B)p\) has stable rank at
   most \(d+1\). Trivialize the projection bundle on each
   characteristic disk. Skeletal restriction has ideal a finite
   sum of \(C_0(\mathbb R^j,D_e)\), with each fiber corner \(D_e\)
   of stable rank one. Torus crossed-product bounds give ideal
   stable rank at most \(j+1\); the extension inequality proves
   the asserted bound by induction.
2. Projection comparison
   \((N-1)[p]\le[1-p]\) supplies actual partial isometries placing
   \(N-1\) orthogonal copies of \(p\) in its complement. Together
   with \(p\), they form a projection \(q\) with
   \(qAq\cong M_N(D)\).
3. Simplicity of the fibers and nonzero \(p(x)\) make \(p\), and
   hence \(q\), full in \(A\). Full-corner K1 invariance therefore
   sends stable nullness in \(A\) back to stable nullness in \(qAq\).
   Rieffel's degree-zero theorem applies because
   \(N\ge d+1\ge\operatorname{sr}(D)\), and contracts the unitary.
4. In the pure case, Seth--Vilalta's function-algebra purity
   theorem gives strict comparison in \(C(X,B)\). A partition of
   unity over local unitary trivializations of \(p\) transfers the
   uniform fiber quasitrace bound to every normalized quasitrace
   on \(C(X,B)\): weighting by a central partition function gives
   a quasitrace on \(B\). The bound
   \((d+1)c<1\) yields \(d\rho(p)<\rho(1-p)\), so strict comparison
   gives the required projection copies.
5. For a based sphere, split evaluation identifies its stable
   class with the reduced K1 class. A final normalization
   \(H(x,t)H(x_0,t)^*\) makes the resulting contraction based.

All prior-art inputs, the full-corner hypothesis, the normalization
for lower semicontinuous quasitraces, and the remaining localization
gap are proved or cited explicitly in the internally reviewed artifact.
