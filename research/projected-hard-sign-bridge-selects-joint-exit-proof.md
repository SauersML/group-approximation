---
rg: 2
id: projected-hard-sign-bridge-selects-joint-exit-proof
kind: route
title: Keep the nonlinear atom as an analytic right compression
target: projected-hard-sign-bridge-selects-joint-exit
requires:
  - mixed-central-cnot-completes-relative-rank-one-router
  - hard-sign-transport-captures-exit-mass
  - product-clock-synchronizes-fanizza-and-e5
  - finite-schur-clifford-packet-flexible-hs-exactification
---

After finite-packet exactification, `H` commutes with the named packet word
`A`, so `(PHS1)` is a projection and `AP=-P`.  Apply `(HST1)` directly with
this `P`; that proof right-multiplies the covariance defect by `P` before
taking Hilbert--Schmidt norm, so it never assumes that `P` is itself a group
word or that the negative support of `A` equals `P` globally.  This gives
`(PHS2)`.

For `H=QF,A=b`, equation `(MCR5)` gives `tau(P)=tau(QF)/2`.  The synchronized
hard bridge identifies the transported source hard word with the E5 pulse at
the same clock level.  This proves hard-sign transport only; first-hit
localization is deliberately not asserted here.

All perturbations used above are fixed finite-packet or polynomial word
telescoping errors.  None depends on matrix dimension, and no support
containment or scalar AND relation was introduced.
