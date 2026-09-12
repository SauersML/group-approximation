---
rg: 2
id: atlas-multiplicity-two-packet-collision-hub-escape-proof
kind: route
title: Verify one literal GL8(2) common-frame escape
target: atlas-multiplicity-two-packet-collision-hub-escape
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_a4_repeated_module_escape_verify.py
  - experiments/atlas-a4-repeated-module-screen.json
---

Decode `(M2E1)` as an `8 x 8` binary matrix.  The verifier checks
invertibility and tests both directions of every H6 and H18 cross edge.
Every left generator retains order two, every right generator retains order
three, and every cross product has cube one.  The triangle presentation maps
onto A4; its only proper nontrivial quotient is C3, which would kill the
involution, so every context image is exactly A4.

Literal multiplication of the stored collision and q14 words gives identity
and nonidentity respectively.  The same multiplication gives the displayed
hub and verifies `h^4=1`, `h^2!=1`.  The regular-representation conclusion
then follows from the canonical trace of a nonidentity finite-group element.
