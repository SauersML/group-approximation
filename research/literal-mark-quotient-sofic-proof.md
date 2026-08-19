---
rg: 2
id: literal-mark-quotient-sofic-proof
kind: route
title: Rerun the block tower without the central sign
target: literal-mark-quotient-sofic
requires: [literal-lamp-kernel-clifford-block-amalgam, finite-telescope-level-coset-orbits]
artifacts: [notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md]
---

## Why sufficient

Theorem 4.3 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`.  The block-amalgam
claim gives `E/<w> = (*_{i in I} (Z/2)^8) semidirect V`, since killing the
amalgamated centre of a free product amalgamated over a central subgroup gives
the free product of the quotients.  Lemma 3.1 of that artifact used only that
the lamp part of the window is finitely generated and residually finite and
that the level acts through a finite permutation group of the sites; both hold
for `M'_J = *_{i in J} (Z/2)^8`, which is a free product of finitely many
finite groups and hence virtually free.  Finite level orbits on blocks make the
window family directed and exhausting, so the shift-free part is locally
residually finite, hence LEF, hence sofic (Lean `LEFSofic.isSofic_of_isLEF`).
Finally `E/<w>` is the `Z`-extension of that part, so it is sofic by
sofic-kernel/amenable-quotient permanence.

`lef-implies-operator-mf` was listed as a prerequisite here in an earlier
version.  It is not needed for the stated target: it gives the MF half of the
LEF consequence, which is a by-product recorded in the claim body, not an input
to soficity.  Dropped so that the declared dependencies of this route are
exactly what its conclusion uses.
