---
rg: 2
id: stw58-cutdown-soft-matrix-copies-contraction-proof
kind: route
title: Combine continuous-field stable-rank bounds with exact Cuntz cutdown matrix copies
target: stw58-soft-support-reservoir-kernel-vanishing
requires: []
artifacts:
  - research/artifacts/stw58-soft-support-orthogonal-reservoir-contraction-2026-09-05.md
---

1. Every hereditary \(D\subset C(X,B)\) has stable rank at most
   \(d+1\). Enlarge it to \(D+C(X)1\), a unital continuous field
   whose fibers have stable rank one. Ng--Sudo's Theorem 1.2,
   cube/torus stable-rank bounds, and the ideal estimate prove
   the assertion.
2. From \((N-1)[h]\le[b]\), Rørdam's exact cutdown lemma gives a
   rectangular row with \(x_i^*x_j=\delta_{ij}(h-\varepsilon)_+\)
   and range positive element in \(\operatorname{Her}(b)\).
   Its polar parts, together with the original cutdown support,
   construct an actual hereditary \(M_N(D_\varepsilon)\subset A\),
   where \(D_\varepsilon=\operatorname{Her}((h-\varepsilon)_+)\).
   Orthogonality \(hb=0\) makes the original support orthogonal
   to all new ranges.
3. A sufficiently small cutdown remains full. Approximate the
   unitary displacement inside \(D_\varepsilon\) and take its
   polar correction; the resulting unitary is homotopic to the
   original one.
4. Full hereditary K1 invariance transfers its zero stable class
   back to \(M_N(D_\varepsilon)\). Rieffel's degree-zero theorem
   contracts it since \(N\ge d+1\ge\operatorname{sr}(D_\varepsilon)\).
   Scalar quotient correction handles nonunital coefficients.
5. In the pure case, a central partition-of-unity argument for
   weighted quasitraces transfers fiber bounds to global ones.
   Blackadar--Handelman's compactness and Lipschitz results make
   the lower dimension bound uniform at a finite positive root.
   Seth--Vilalta function-algebra purity and strict comparison
   then give the required Cuntz inequality.
6. Split evaluation identifies based stable sphere classes with
   reduced K1, and \(H(x,t)H(x_0,t)^*\) makes the contraction based.

The internally reviewed artifact supplies the exact hereditary
matrix-image proof, full-cutoff argument, quantitative norm control,
and precise primary citations. General kernel localization is not
assumed or concluded.
