---
rg: 2
id: subtree-independence-from-expander-placement
kind: route
title: Relative tensor placement turns the fixed expander into sibling independence
target: subtree-trace-independence-certificate
requires:
  - subtree-expander-relative-factor-placement
  - expander-separated-factors-have-independent-traces
  - toeplitz-head-jacobi-words-give-uniform-expanders
---

Use the relative factorization supplied by the placement claim on the retained
carrier.  The Jacobi words give one `lambda<1` independent of level.  Apply
`(ESF1)` to the two sibling signs.  Their commutator energy and spin-factor
placement errors are `O(E)` and `O(sqrt(E))`, respectively, so the covariance
is `O(sqrt(E))`.  The discarded carrier has trace `O(E)` and changes each
normalized trace pairing by `O(sqrt(E))` after Cauchy--Schwarz.  This gives
`(STI1)` with dimension- and depth-independent constants.
