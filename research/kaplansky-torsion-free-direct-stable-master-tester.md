---
rg: 2
id: kaplansky-torsion-free-direct-stable-master-tester
kind: claim
title: The two-generator torsion-free master separately tests direct and stable finiteness
distinct_from:
  kaplansky-direct-stable-finiteness-one-universal-group: that uses a torsionful universal host and quantifies over all groups, allowing direct and stable finiteness to collapse; this uses the torsion-free master, quantifies only over torsion-free groups, and keeps the two properties separate.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that tests domains, idempotents, and two-sided units; this tests one-sided inverses in scalar and every matrix size.
  two-generator-fp-torsion-free-master-tester: that packages the earlier Whitehead, assembly, class, and three Kaplansky tests but does not include direct or stable finiteness.
---

There exists one two-generator finitely presented torsion-free group `E`,
independent of the coefficient field and simultaneously nonsofic and non-MF,
such that for every field `k` the following equivalences hold separately:

1. `k[E]` is directly finite iff `k[G]` is directly finite for every
   torsion-free group `G`.
2. `k[E]` is stably finite iff `k[G]` is stably finite for every
   torsion-free group `G`.

For either property `P`, the all-coefficient assertion has the exact
finite-field reduction

```text
P(k[G]) for every field k and every torsion-free group G
  <=>
P(F[E]) for every finite field F.
```

For stable finiteness the finite-field side reduces further to prime fields:

```text
F[E] is stably finite for every finite field F
  <=>
F_p[E] is stably finite for every prime p.
```

These are exact reductions, not proofs that the test rings are directly or
stably finite. No equivalence between direct and stable finiteness in the
torsion-free lane is asserted.

**ESTABLISHED 2026-08-30** by
[[kaplansky-tf-direct-stable-master-tester-proof]].
