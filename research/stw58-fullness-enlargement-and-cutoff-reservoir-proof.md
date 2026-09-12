---
rg: 2
id: stw58-fullness-enlargement-and-cutoff-reservoir-proof
kind: route
title: Enlarge a small support by a tiny full endpoint diagonal and manufacture the reservoir after cutoff
target: stw58-small-quasitrace-support-kernel-vanishing
requires:
  - stw58-soft-support-reservoir-kernel-vanishing
artifacts:
  - research/artifacts/stw58-small-quasitrace-support-kernel-contraction-2026-09-05.md
---

1. Lin's stable-rank-one theorem and almost divisibility give the
   finite-matrix inequalities for Rørdam--Winter Proposition 5.1.
   A unital prime dimension-drop map has a nonzero order-zero
   endpoint map from \(M_n\) or \(M_{n+1}\). One diagonal image
   is a nonzero full positive element \(c\) with
   \(d_\tau(c)\le1/n\) for every normalized quasitrace.
2. Given \(\Delta(h)<1/N\), choose such a constant \(c\) small
   enough that \(H=h+c\) satisfies \(\Delta(H)\le\gamma<1/N\).
   Then \(H\) is full and \(\operatorname{Her}(h)\subseteq
   \operatorname{Her}(H)\), without requiring a projection.
3. For small \(\varepsilon>0\), let
   \(a=(H-\varepsilon)_+\) and \(b=(\varepsilon/2-H)_+\).
   The first remains full, the two are orthogonal, and restriction
   of each quasitrace to \(C^*(H(x),1)\) gives
   \(d_\tau(a(x))\le\gamma\) and \(d_\tau(b(x))\ge1-\gamma\).
   In particular \(b\) is nonzero at every fiber and hence full.
4. The reviewed transfer from uniform fiber bounds to global
   quasitraces, together with purity of \(C(X,B)\) and strict
   comparison, gives \((N-1)[a]\le[b]\). This comparison uses
   \(N\gamma<1\), not a dimension-dependent stable range.
5. Approximate \(u-1\) in \(\operatorname{Her}(a)\) and use polar
   repair to obtain a homotopic unitary supported there. Taking
   \(N=d+1\), the required reviewed reservoir theorem contracts
   it. Normality puts \(u-1\) in \(\operatorname{Her}(|u-1|)\);
   the usual basepoint normalization makes sphere contractions based.

The internally reviewed artifact includes the full proof and a
small-trace essential hereditary example in a UHF algebra whose
original support has zero annihilator. The example shows why the
orthogonal reservoir must be created after cutoff. It is not an
example of a nonzero unstable kernel.
