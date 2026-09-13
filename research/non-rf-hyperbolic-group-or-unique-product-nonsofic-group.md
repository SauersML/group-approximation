---
rg: 2
id: non-rf-hyperbolic-group-or-unique-product-nonsofic-group
kind: claim
title: Either some hyperbolic group is not residually finite, or some nonsofic group has unique products
distinct_from:
  non-residually-finite-hyperbolic-group: that is Gromov's open question; this is an unconditional disjunction whose other branch is a nonsofic group with unique products.
  unique-product-non-sofic-group: that is the open existence question; this says it follows from a positive answer to Gromov's question for one explicit host.
---

**ESTABLISHED.**  At least one of the following holds.

1. The hyperbolic Kazhdan cover `G` of the binary Leavitt unit group
   (`hyperbolic-kazhdan-cover-of-leavitt-unit-group`) is not residually finite.
   So some word-hyperbolic group is not residually finite, the negative answer
   to Gromov's question (`non-residually-finite-hyperbolic-group`).
2. There is a finitely generated, torsion-free nonsofic group `W` with unique
   products.  For every field `K`, the group ring `K[W]` is a domain with only
   trivial units, hence directly finite.

Branch 2 is explicit.  Take a deep normal finite-index subgroup `G_k` of `G`
and restrict the Leavitt rigid pair to it.  `W` is the integer-lamp wreath over
the restricted pair.

Derivation: `non-rf-hyperbolic-group-or-unique-product-nonsofic-group-proof`.
Status: unreviewed.  Neither branch is claimed to hold on its own.
