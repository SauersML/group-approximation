---
rg: 2
id: mixed-cnot-joint-exit-via-projected-hard-sign
kind: route
title: Compress only the hard bridge by the joint exit and return its complement separately
target: mixed-cnot-joint-exit-first-hit-transducer
requires:
  - projected-hard-sign-bridge-selects-joint-exit
  - mixed-cnot-allowed-active-return
  - free-root-sign-atoms-transport-with-linear-hs-loss
---

Use the joint packet projection only as the right compression in the hard
intertwiner estimate.  This sends exactly the violating exit to its E5
first-hit layer and is insensitive to allowed negative hard-sign sectors.
Return the complementary carrier by `mixed-cnot-allowed-active-return`.

This route avoids the stronger three-context failure certificate.  Its sole
open content is now coherence of the active complement, rather than scalar
selection of the exit.
