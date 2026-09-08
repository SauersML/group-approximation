---
rg: 2
id: split-ca-quantum-defect-proof
kind: route
title: Compute finite matrix entries and translate a missing pattern away from every local operator
target: split-ca-quantization-has-sharp-defect
requires: []
artifacts:
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
  - research/artifacts/check-gottschalk-quantum-compression-2026-09-07.py
  - research/artifacts/gottschalk-quantum-compression-replay-2026-09-07.json
---

Sections 1-5 of the artifact prove the claim. Equality of encoded
configurations off F forces their inputs to agree off F M^(-1). The
remaining matrix-entry calculation needs only F M^(-1) N^(-1) N,
giving the locality of the unital completely positive compression.

Translate a finite configuration outside the encoder image away from
the support of any local operator. Its diagonal expectation agrees with
that of the constant image configuration, while the range projection
has expectations zero and one. This gives the lower bound 1/2, attained
by I/2. A local unitary sending that constant configuration to the
excluded one gives a norm-one multiplicative defect of the compression.

Finally a unital homomorphism extending the diagonal pullback would
kill a nonzero cylinder's diagonal matrix unit. The finite matrix-unit
identities would then make it kill the identity, a contradiction.
In the onto case V is unitary and conjugation gives the required local
isomorphism. No general surjunctivity assumption is used in these proofs.
