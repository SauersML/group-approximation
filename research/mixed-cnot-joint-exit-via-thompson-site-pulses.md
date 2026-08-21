---
rg: 2
id: mixed-cnot-joint-exit-via-thompson-site-pulses
kind: route
title: Send projected mixed-CNOT exits to independent Thompson first-hit sites
target: mixed-cnot-joint-exit-first-hit-transducer
requires:
  - projected-hard-sign-bridge-selects-joint-exit
  - thompson-site-pulses-localize-hard-exits
  - fanizza-hard-exits-attach-to-thompson-site-pulses
  - mixed-cnot-allowed-active-return
  - branching-plus-first-hit-exits-forces-hs-floor
---

Use the projected hard-sign bridge to isolate the literal joint exit inside
the current active carrier.  The finite incidence claim identifies its hard
word with the source half of the local doubled site packet.  The site swap
then maps it into `X_n` while commuting with every earlier pulse, and the
orthogonal first-hit trace budget pays the exits.  Return the complementary
allowed/active carrier through the existing S3 obligation and apply the
branching first-hit ledger.
