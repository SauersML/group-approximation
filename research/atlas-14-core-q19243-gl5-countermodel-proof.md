---
rg: 2
id: atlas-14-core-q19243-gl5-countermodel-proof
kind: route
title: Direct finite-matrix verification of the GL5(2) core countermodel
target: atlas-14-core-q19243-gl5-countermodel
requires: []
artifacts:
  - experiments/atlas_a4_gl5_core_collision_countermodel.py
  - research/artifacts/atlas-a4-gl5-core-collision-countermodel.json
---

## Exact finite verification

Decode the row-major binary matrix `h` in `(A4-GL5-1)`.  Gaussian elimination
over `F2` verifies that it is invertible.  The verifier reconstructs the
fourteen-word core from the canonical packet, substitutes

```text
factor 1: g |-> diag(g,1),
factor 2: g |-> h diag(g,1) h^-1,
```

and multiplies every matrix over `F2`.  It asserts that all fourteen pair
products have cube one and that collision `19243` itself is the identity.
As an independent boundary check it reconstructs all thirty packet words and
finds exactly fourteen satisfied, so the witness is not accidentally one of
the 202 full-packet positions already classified by the earlier screen.

The verifier then evaluates the conjugation cocycle for each of the four
`H_6` and four `K=Q_SECOND` generators.  All eight are nonidentity; the first
has order two and hexadecimal matrix certificate

```text
01000000000001010000000001000000000001000000010001.
```

This proves `(A4-GL5-3)` directly.  In the normalized regular trace every
nonidentity group element has trace zero, so its distance from the identity is
exactly `sqrt(2)`.  Finally

```text
||[U,g]||_2 = ||[(U-V),g]||_2 <= 2||U-V||_2
```

for every `V` in the rank-three commutant.  This proves `(A4-GL5-4)` and the
claim.  No numerical tolerance or finite-precision step enters the audit.
