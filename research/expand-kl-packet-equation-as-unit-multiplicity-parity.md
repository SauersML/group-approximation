---
rg: 2
id: expand-kl-packet-equation-as-unit-multiplicity-parity
kind: route
title: Expand the transported involution packet and collect equal group-basis units
target: kl-gate-corner-test-is-an-even-unit-fiber-audit
requires:
  - canonical-left-comb-kl-gate-is-a-mixed-involution
  - both-rank-three-factors-must-be-packet-corrected
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Because `qhat=qhat^-1`, the two packet corrections coincide.  Substitute
into the bilinear correction equation and expand in the group basis.
Characteristic two makes equality exactly even multiplicity in every unit
fiber.  Evaluation of the total expression is zero independently of these
fibers, so the certificate must compare the individual unit values.  Bergman
normal form supplies that comparison and rejects all twenty cyclic KL gates
and all 380 coefficient-one roots.
