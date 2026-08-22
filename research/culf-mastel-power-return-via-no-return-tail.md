---
rg: 2
id: culf-mastel-power-return-via-no-return-tail
kind: route
title: Feed the block-encoded acceptance contraction into a canonical no-return tail
target: culf-mastel-positive-density-power-return
requires:
  - finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
  - block-encoded-acceptance-still-needs-corner-return
  - pauli-zero-atom-removes-acceptance-source-deficit
  - canonical-positive-density-no-return-dilation-tail
---

Use the finite-game construction to obtain the strict NONHALT contraction
`T_m`, and its finite-control block encoding.  The Pauli-zero theorem removes
the raw source-mass deficit.  The no-return tail performs the still-missing
orientation/capacity identification, makes `T_m=q_mW_mq_m`, and obtains
`(CPR1)` through the one prescribed length `N_mL_m`.  The finite packet fixes
`alpha_m=tau(q_m)>0`; perfect
completeness makes `T_m` the identity on the exact accepted carrier, so its
properly infinite amplification extends down the tail.  These are clauses
1--4 of `culf-mastel-positive-density-power-return`.
