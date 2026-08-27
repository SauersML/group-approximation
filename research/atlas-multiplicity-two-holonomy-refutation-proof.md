---
rg: 2
id: atlas-multiplicity-two-holonomy-refutation-proof
kind: route
title: Evaluate the two raw S3 opcodes in the regularized GL8 frame
target: atlas-multiplicity-two-refutes-holonomy-coherence-gap
requires:
  - atlas-multiplicity-two-packet-collision-hub-escape
  - atlas-a8-four-cycle-controls-raw-s3-energy
artifacts:
  - experiments/atlas_a4_repeated_module_escape_verify.py
---

The raw-S3 dictionary identifies the two involutions as `t21` and `t12`.
The verifier lifts them to the repeated natural `8`-dimensional module,
conjugates by the stored frame, and checks that both relative covariance
opcodes are nonidentity of exact order four.  In the left regular
representation of the finite generated group, every nonidentity element has
normalized trace zero.  Since the opcodes are unitary, each squared distance
from the identity is therefore two, proving `(M2H2)`.

The packet verifier already checks every mixed context is an exact A4 and
that collision `19243` is the identity.  Taking those literal mixed pairs as
the context-vertex representations makes both cyclic edge maps literal
equalities, hence permits identity stable letters.  Restriction of a regular
group representation to a subgroup is a multiple of that subgroup's regular
representation, giving exactly the required A8 and A4 normalized types.
