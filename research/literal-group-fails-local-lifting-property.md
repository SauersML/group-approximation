---
rg: 2
id: literal-group-fails-local-lifting-property
kind: claim
title: The full C*-algebra of the literal group fails Kirchberg's local lifting property
refuted_by: [literal-group-local-lifting-property]
distinct_from:
  literal-group-local-lifting-property: that is the refuted positive statement; this is its negation, separated so the subgroup obstruction can be a reusable established claim.
  literal-group-lacks-factorization-property: failure of LLP does not imply failure of the factorization property (SL_3(Z) itself separates them); this claim therefore kills only the LLP route to factorization.
artifacts:
  - GroupApproximation/Analysis/NuclearityBaseEmbedding.lean
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

The literal finitely presented group `E` satisfies

```text
C*(E) does not have Kirchberg's local lifting property.          (ELLP1)
```

Indeed, the established split normal form gives

```text
E = N_E semidirect_product V,
V = (Z[1/2]^3 semidirect_product SL_3(Z)) semidirect_product Z.
```

Thus `E` contains a subgroup isomorphic to `SL_3(Z)`.  By
Ioana--Spaas--Wiersma, Corollary B (arXiv:2006.01874), the full group
C*-algebra `C*(SL_3(Z))` does not have LLP.  Their Remark 1.2 proves that LLP
for full group C*-algebras passes to subgroups.  Hence LLP for `C*(E)` would
force LLP for `C*(SL_3(Z))`, a contradiction.

This obstruction is compatible with `E` still having Kirchberg's
factorization property: Ioana--Spaas--Wiersma explicitly note that
`SL_3(Z)` is residually finite and has the factorization property despite
failure of LLP.  Accordingly `(ELLP1)` invalidates only
`literal-fp-via-llp`, not every possible route to the factorization property.

Proof: `literal-group-llp-failure-via-sl3-subgroup`.
