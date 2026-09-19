---
rg: 2
id: iwahori-outlier-repair-via-nielsen-transport
kind: route
title: Reduce the Iwahori outlier to operator transport integralization and Nielsen transversality
target: iwahori-outlier-repair
requires: [mixed-intertwiner-energy-transport-localization, iwahori-commensurator-nielsen-involution, iwahori-fractional-transport-integralization, iwahori-nielsen-extension-transversality]
artifacts:
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
  - notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md
---

Start with a central-regular negative sequence at the Iwahori endpoint.  The
identity identification between the two exact edge restrictions is an almost
intertwiner, so `mixed-intertwiner-energy-transport-localization` applied to
its two isotypic decompositions gives an exact physical-mass transportation
plan.  If `E_n` is the total edge energy, choose `a_n->0` with
`E_n/a_n->0`.  Then all but `o(1)` transport mass lies on block pairs whose
mixed spectral bottom is at most `a_n`.

The first open prerequisite,
`iwahori-fractional-transport-integralization`, turns this fractional
low-gap plan into actual orthogonal matched physical summands, after only
`o(d_n)` deletion/padding, and supplies a direct sum of near-unitary
almost-intertwiners on those summands.  The established index-three branching
theorem in the cited artifact ensures that passing between a modular vertex
irreducible and its Iwahori constituents has uniformly bounded local degree
and no hidden restriction multiplicity.

It remains to correct each matched near-unitary pair to the common extension
locus.  `iwahori-commensurator-nielsen-involution` identifies the two
opposite modular extension loci, after an inner conjugacy, as a single locus
`E` and its image `alpha^*E` under the explicit involution

```text
alpha(u)=u^(-1)e,
alpha(e)=u^(-1)e u.
```

The second open prerequisite, `iwahori-nielsen-extension-transversality`,
provides the required dimension-free local correction for every matched pair.
Taking the orthogonal direct sum of those corrected pairs, and restoring the
`o(d_n)` exceptional dimensions allowed by flexible matching, produces an
exact invertible edge intertwiner between stabilized modular vertex
representations at normalized-HS distance `o(1)` from the original pair.
That is exactly `iwahori-outlier-repair`.

The reduction separates two phenomena that were previously bundled into the
word "outlier":

1. **fractional-to-integral operator matching** of the physical mass; and
2. **metric transversality** of one modular restriction locus against its
   explicit Nielsen-involutive image.

Spectral localization itself is no longer a missing input.
