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
  - free-root-first-detection-eigenvectors-localize-exactly
  - finite-schur-clifford-packet-flexible-hs-exactification
---

After finite-packet exactification, `H` commutes with the named packet word
`A`, so `(PHS1)` is a projection and `AP=-P`.  Apply `(HST1)` directly with
this `P`; that proof right-multiplies the covariance defect by `P` before
taking Hilbert--Schmidt norm, so it never assumes that `P` is itself a group
word or that the negative support of `A` equals `P` globally.  This gives
`(PHS2)`.

For `H=QF,A=b`, equation `(MCR5)` gives `tau(P)=tau(QF)/2`.  The synchronized
hard bridge identifies the transported source hard word with the E5 top root
at the same clock level.  The source-fixed symmetric frame supplies the lower
trivial character data, so the first-detection theorem puts `UP` in that
level's Fourier boundary.  The boundary layers are summable independently of
any extra negative spectral mass outside `UP`.

All perturbations used above are fixed finite-packet or polynomial word
telescoping errors.  None depends on matrix dimension, and no support
containment or scalar AND relation was introduced.
