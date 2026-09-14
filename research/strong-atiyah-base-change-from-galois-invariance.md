---
rg: 2
id: strong-atiyah-base-change-from-galois-invariance
kind: claim
title: Galois-invariant von Neumann ranks carry Strong Atiyah from algebraic to complex coefficients
distinct_from:
  strong-atiyah-base-change-algebraic-to-complex: that is the open implication for all torsion-free groups at once; this is the established group-by-group implication under a rank-invariance hypothesis.
  vn-rank-galois-invariant-for-torsion-free-groups: that is the open invariance hypothesis; this is the theorem that consumes it.
---

**Theorem.**  Let `G` be a torsion-free group.  Suppose that for every
`r >= 0` the group `G x Z^r`

1. satisfies Strong Atiyah over `Qbar`, and
2. has Galois-invariant kernel dimensions: `dim ker r_(sigma(A)) = dim ker r_A`
   for every `A` over `C[G x Z^r]` and every automorphism `sigma` of `C` fixing
   `Qbar`.

Then `G` satisfies Strong Atiyah over `C`.

**Corollary (one group).**  Let `E` be the master tester of
`two-generator-fp-torsion-free-master-tester`.  If `E` satisfies Strong Atiyah
over `Qbar` and has Galois-invariant kernel dimensions, then `E` satisfies
Strong Atiyah over `C`.  The reason: `E x Z^r` is finitely presented and
torsion-free, so it embeds in `E`, and both hypotheses pass to subgroups.  Then
every countably generated recursively presented torsion-free group satisfies
Strong Atiyah over `C`, and `C[G]` embeds in a division ring for every
torsion-free `G` (`division-ring-embedding-torsion-free-one-group-tester`).

**ESTABLISHED 2026-09-12** by [[galois-invariance-base-change-proof]].
