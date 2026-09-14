---
rg: 2
id: separated-pairing-decoder-proof
kind: route
title: Agreement-score means, a separation margin, and bounded differences
target: separated-pairing-families-admit-noisy-decoders
requires: []
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

Section 4 of the artifact.

* **Means.** A pair of `sigma` that is also a pair of `pi` agrees with
  probability `1/m + lambda`, where `lambda = (1-1/m) rho^2`. Any other pair
  agrees with probability `1/m`. So `E S_sigma = 1/m + lambda ov(sigma,pi)`.
* **Concentration.** Changing one pair symbol moves `S_sigma` by at most `4/N`,
  and changing one noise variable by at most `2/N`. McDiarmid's inequality gives
  one-sided tails `exp(-N T^2/6)`.
* **Decoding.** At the threshold `1/m + lambda (1 - delta_0/2)`, a union bound
  over `|P|` events with `T = lambda delta_0/2 >= rho^2 delta_0/4` gives the
  stated error.
* **Shift invariance.** Every score is unchanged by adding a constant symbol.
