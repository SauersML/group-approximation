---
rg: 2
id: hecke-frame-failure-dual-proof
kind: route
title: Separate the cone of right moduli from the unit
target: hecke-frame-failure-has-right-multiplier-dual
requires:
  - hecke-top-spectrum-coverage-controls-window
---

Normalize a nonzero element of the cone by trace.  Because
\(\tau(\sum_jA_j^*A_j)=\sum_j\|A_j\|_2^2\), the trace-one slice is the
convex hull of the compact unit-sphere image \(A\mapsto A^*A\); it is
compact.  This makes the whole positive cone closed.

If the cone misses \(1\), strong finite-dimensional separation supplies a
real functional which is positive at \(1\) and nonpositive on the cone.
Trace duality writes it as \(C\mapsto\tau(ZC)\) with \(Z=Z^*\).  The
identity

\[
\tau(ZA^*A)=\langle A,R_ZA\rangle
\]

turns nonpositivity on every generator into
\(P_{\cal H}R_ZP_{\cal H}\preceq0\).  The converse is immediate.  Applying
this to the spectral subspace and invoking the prerequisite gives the
stated positive/dual alternative.
