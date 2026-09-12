---
rg: 2
id: complete-graph-clifford-cover-center-dies-in-finite-quotients
kind: claim
title: In the complete-graph Kun--Thom Clifford cover every finite quotient kills the central involution
distinct_from:
  separated-finite-normal-subgroups-preserve-surjunctivity: that handles finite normal subgroups that inject into some finite quotient; this shows the Clifford center injects into none, so that theorem does not apply.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

Let `S` be the complete graph on `X = G/Gamma`, for the Kun--Thom Theorem E pair, and `E_S` the Clifford
cover with central involution `eps`. Every homomorphism from `E_S` to a finite group kills `eps`.

Proof: artifact Section 2. If `eps` maps to `z != 1`, any two distinct lamps have images with commutator
`z`. So the images of the infinitely many lamps are pairwise distinct, which is impossible in a finite
group.
