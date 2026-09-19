---
rg: 2
id: dinur-schur-amplification-feeds-toeplitz-tail
kind: route
title: Amplify residual forbidden mass before returning it through the one-swap Toeplitz head
target: toeplitz-tail-retains-contextual-schur-density
requires:
  - dinur-linear-size-constraint-gap-amplification
  - classical-pcp-gap-is-not-tracial-pvm-gap
  - hs-schur-packet-gap-amplification
  - toeplitz-tail-plus-one-swap-generates
  - toeplitz-finite-head-centralizes-deep-tail
  - schur-child-crosses-toeplitz-compressor
  - contractive-computation-ladder
---

Apply `(HPA1)` inside the residual coefficient algebra which erased the
current head Reynolds range. Composition keeps the packet scale fixed, while
powering makes the surviving forbidden mass dominate the fixed loss incurred
when the one Toeplitz head swap returns it to the ambient carrier. If return
still fails, identify the residual tail by the explicit compression and
repeat. The amplified mass gives the strict contraction required by the
contractive ladder; bounded overlap keeps the total HS charge independent of
depth.
