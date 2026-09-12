---
rg: 2
id: division-ring-embedding-torsion-free-one-group-tester
kind: claim
title: One two-generator nonsofic group tests division-ring embeddability of torsion-free group algebras over each field
distinct_from:
  two-generator-fp-torsion-free-master-tester: that tests the domain, idempotent and unit properties through finite patterns; this tests embeddability into a division ring, a priori stronger than being a domain, through a colimit of integer-valued rank functions.
  raag-out-mcg-virtual-all-field-division-rings: that proves division-ring embeddings for explicit geometric classes; this is a one-group equivalence for all torsion-free groups and proves no embedding by itself.
  higman-group-sterile-yet-division-embeddable: that is division-ring embeddability of one specific group; this is a universal tester for the property.
---

Let `E` be the two-generator finitely presented torsion-free group of
`two-generator-fp-torsion-free-master-tester`, which may be chosen nonsofic
and non-MF.  For every field `K`, separately,

```text
K[E] embeds in a division ring   <=>   K[G] embeds in a division ring
                                        for every torsion-free group G.
```

## Corollary: Strong Atiyah at one group, with no determinant hypothesis

Let `K` be a subfield of `C`.  If `E` satisfies the Strong Atiyah Conjecture
over `K`, then `K[G]` embeds in a division ring for every torsion-free group
`G`; in particular every such `K[G]` is a domain.  The reason: by Linnell's
theorem, as quoted in `strong-atiyah-torsion-free` from Fisher--Ng
(arXiv:2606.19606, Section 1.1), Strong Atiyah over `K` for `E` makes the
division closure of `K[E]` in `U(E)` a division ring containing `K[E]`, and the
tester transfers the embedding to every torsion-free group.

Contrast `algebraic-atiyah-and-determinant-one-group-tester`: there the
analytic conclusion, integral von Neumann ranks for all torsion-free groups,
needs the determinant conjecture as well.  The algebraic conclusion here needs
nothing further, because integer-valued rank functions survive directed
colimits without any spectral control.

Contrapositive: a torsion-free group `G` and a subfield `K` of `C` for which
`K[G]` embeds in no division ring would refute Strong Atiyah over `K` for the
single group `E`.

**ESTABLISHED 2026-09-11** by [[division-ring-embedding-colimit-tester-proof]].
