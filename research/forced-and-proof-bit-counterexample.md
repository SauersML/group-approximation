---
rg: 2
id: forced-and-proof-bit-counterexample
kind: route
title: Append one AND bit to a perfect PCPP proof without weakening soundness
target: dfnqxy-pcpp-contract-allows-nonlinear-proof-views
requires:
  - dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
  - hadamard-pcpp-reflects-affine-unsafety
---

Conjoin any PCPP verifier with the three-query check
`b=z_1 AND z_2`, where `b` is one appended proof coordinate.  Perfect
completeness is retained by choosing the forced bit, while soundness can
only improve.  On the affine four-point diagonal answer support, the honest
Hadamard coordinates `z_1,z_2` run through `F_2^2`.  The three responses at
`00,01,10` all have `b=0`, but their odd xor has visible value `11` and
still has `b=0`, so the augmented predicate rejects it.  Thus the permitted
PCPP has a nonlinear honest proof view over an affine source.

