---
rg: 2
id: stw58-fixed-spectral-point-small-support-localization
kind: claim
title: A fixed spectral point without a heavy atom globally localizes a unitary family into small support
distinct_from:
  stw58-small-quasitrace-support-kernel-vanishing: gives an explicit global homotopy into small support from a spectral atom bound instead of assuming small support initially.
artifacts:
  - research/artifacts/stw58-fixed-spectral-point-global-localization-2026-09-05.md
---

Let \(B\) be nonzero simple unital finite pure with
\(QT_1(B)\ne\varnothing\), let \(X\) be compact metric of dimension
\(d\ge1\), and let \(u\in U(C(X,B))\). Write \(\mu_{x,\tau}\)
for the spectral probability measure of \(u(x)\) under \(\tau\).

If some \(\lambda\in\mathbb T\setminus\{1\}\) satisfies
\[
 \mu_{x,\tau}(\{\lambda\})<1/(d+1)
 \quad\text{for every }x,\tau,
\]
then one fixed proper arc supports a degree-one function \(f\)
with \(f(1)=1\), and there is a real continuous \(L\) with \(L(1)=0\),
such that
\[
 u=f(u)\exp(iL(u)),\qquad
 \sup_{x,\tau}d_\tau(|f(u(x))-1|)<1/(d+1).
\]
The resulting explicit homotopy to \(f(u)\) is based whenever \(u\)
is based. If the stable \(K_1\)-class is zero, the family contracts.

For \(X=S^k\), the class belongs to the canonical stable summand
\(I_k(B)\). Consequently every representative of a class outside
that summand must, at every \(\lambda\ne1\), have an atom of mass
at least \(1/(k+1)\) for some parameter and quasitrace.

The spectral condition need not hold even for contractible scalar
families. The result does not provide unrestricted fragmentation
or solve the general LVIII kernel question.

ROUTES:

- stw58-uniform-spectral-arc-and-degree-one-squeezing-proof
