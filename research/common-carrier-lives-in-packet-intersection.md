---
rg: 2
id: common-carrier-lives-in-packet-intersection
kind: claim
title: A common algebraic carrier lives in the literal packet-subgroup intersection
distinct_from:
  affine-frobenius-common-negative-carrier: that asks for a common projection while preserving the global verifier budget; this identifies where any such projection is forced to live once the finite context packets embed in one ambient group.
  finite-support-one-sided-stabilizers-are-torsion: that analyzes a literal group element fixing one finite-support coefficient; this is the elementary but stronger support-intersection statement for one additive coefficient belonging to several packet group algebras.
---

**ESTABLISHED.**  Let `K` be a field, let `Gamma` be a group, and let
`H_1,...,H_m` be subgroups.  Inside the canonical group algebra,

```text
intersection_i K[H_i]=K[intersection_i H_i].           (CPI1)
```

Consequently, suppose the finite affine-Frobenius context groups `H_c`
embed in an ambient group `Gamma` and a common negative carrier satisfies

```text
p_x=((1-A_(c,x))/2)q_(c,x) in K[H_c]                 (CPI2)
```

for every context containing `x`.  Then

```text
p_x in K[K_x],
K_x=intersection_(c contains x) H_c.                  (CPI3)
```

In particular `K_x` is finite and the shared reflection
`B_x=1-2p_x` already lies in one literal finite packet-subgroup overlap.

Thus the high-density common-carrier reduction cannot be implemented by
placing independent packet coefficients in general position and hoping for
additive cancellation.  The packet embeddings themselves must be arranged
with a finite subgroup overlap carrying `p_x`.  If these overlaps are glued
only along a tree, the construction remains in the existing finite
Bass--Serre class.  A successful strict-budget construction must therefore
use cyclic holonomy or another genuinely non-Bass--Serre relation while
preserving all packet embeddings.
