---
rg: 2
id: factorization-and-canonical-qd-are-finitely-local-proof
kind: route
title: Identify the full group algebra as the directed union of full subgroup algebras
target: factorization-and-canonical-qd-are-finitely-local
requires:
  - directed-unions-preserve-trace-approximations
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

For every subgroup `H<=G`, the algebraic inclusion `C[H] -> C[G]` is
isometric for the full norms.  Indeed, given any unitary representation `pi`
of `H`, the induced representation `Ind_H^G(pi)`, restricted to the subspace
over the identity coset, contains `pi`; hence the full `G`-norm of an element
of `C[H]` is at least its norm in every representation of `H`.  The reverse
inequality follows by restricting representations of `G`.  Therefore

```text
C*(H) -> C*(G)                                         (1)
```

is injective, and the canonical traces agree under (1).

The finitely generated subgroups of `G` form an upward directed family and
their group rings exhaust `C[G]`.  Thus `C*(G)` is the norm closure of the
directed union of their full group algebras.  The directed-union trace theorem
makes amenability, and separately quasidiagonality, equivalent to the
corresponding property on every finitely generated stage.  Brown's Theorem
4.1.9 identifies amenability of the full canonical trace with Kirchberg's
factorization property, proving (1) and (2) of the claim.

If the full canonical trace of `G` is amenable but not QD, every restriction
is amenable, while finite locality of QD forces at least one finitely generated
restriction not to be QD.  This proves the last assertion.

**Trust boundary.**  Brown's factorization/amenable-trace equivalence is
imported.  Full-norm subgroup injectivity, trace compatibility, and directed
density are proved above.
