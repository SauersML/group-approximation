---
rg: 2
id: scalar-trace-of-diagonal-normalizer-is-permutation-blind
kind: claim
title: Scalar trace of a diagonal normalizer does not control its permutation displacement
distinct_from:
  diagonal-normalizer-rigidity: that rounds approximate normalizers of a fixed full diagonal masa to monomial matrices; this shows that even an exact monomial normalizer's scalar trace does not control the Hamming displacement of its permutation part.
  dephasing-destroys-multiplicativity: that loses interference before a coherent normalizer has been extracted; this obstruction remains after exact diagonal normalization and lives in the diagonal phase.
  approximate-bernoulli-lamp-extraction-is-cartan-completion: that identifies the global invariant-diagonal extraction gate; this gives the elementary conditional-expectation firewall explaining why scalar regular-character data cannot replace that gate.
artifacts:
  - research/artifacts/universal-hilbert-schmidt-obstruction-integration-2026-08-22.md
---

**ESTABLISHED.**  Scalar trace cancellation can be carried entirely by the
phase part of an exact diagonal normalizer.  For even `d`, let

```text
u_d=diag(1,...,1,-1,...,-1),                            (STP1)
```

with `d/2` entries of each sign.  Then `u_d` normalizes the diagonal masa
`D_d` and

```text
tr_d(u_d)=0,                                            (STP2)
```

but the permutation component of the monomial unitary `u_d` is the identity.
Its induced permutation therefore has Hamming displacement zero, the exact
opposite of the separation that a regular-trace sofic model would need.

The missing datum is diagonal conditional expectation.  A genuine
off-diagonal groupoid normalizer `v` is controlled by

```text
E_(D_d)(v)=0,                                           (STP3)
```

whereas `(STP1)` satisfies `E_(D_d)(u_d)=u_d` despite `(STP2)`.  Thus a
Cartan classicalization must preserve conditional expectation and coherent
normalizer multiplication; scalar traces plus diagonal normalization are
insufficient.

