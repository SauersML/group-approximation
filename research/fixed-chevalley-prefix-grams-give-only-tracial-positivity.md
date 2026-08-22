---
rg: 2
id: fixed-chevalley-prefix-grams-give-only-tracial-positivity
kind: claim
title: Fixed Chevalley prefix Gram matrices are tracially positive but do not supply a ucp generator lift
artifacts:
  - research/artifacts/fixed-chevalley-prefix-gram-ucp-fence-2026-08-21.md
distinct_from:
  maslov-sector-tracial-generator-ucp-liftability: that asks for honest coordinate ucp maps on the canonical root-generator operator system; this proves only approximate affine consistency of fixed positive prefix Gram matrices and identifies the missing simultaneous positivity condition.
  positive-cycle-near-unitary-edges-force-trivial-holonomy: that extracts an energy bound after one honest positive labelled cycle has been supplied; this explains why Chevalley word defects alone do not supply that labelled cycle.
---

Let `U_n(s)` be unitary Chevalley microstates.  For every fixed finite family
of root words `p_1,...,p_m`, the prefix Gram matrix

```text
G_n(i,j)=U_n(p_i)^*U_n(p_j)
```

is exactly positive with diagonal one.  Every equality between two entries
which has a fixed bounded-area derivation from the Kassel relations holds in
normalized Hilbert--Schmidt norm up to the corresponding bounded sum of
relator defects.  In particular, the explicit quarter-turn and rank-one
braid derivations make the fixed root atlas asymptotically label-consistent.

This gives only

```text
G_n >= 0,                 dist_2(G_n,L_atlas) -> 0,
```

where `L_atlas` is the affine space imposing exact equality on repeated root
labels.  A ucp lift needs an **honest** matrix in
`M_m(M_(d_n))_+ intersect L_atlas`, coherently for all word sets and all
matrix levels.  Projecting onto `L_atlas` can create negative spectrum;
clipping that spectrum destroys the label equalities.  The Chevalley
relations control the size of those failures in normalized `2`-norm but do
not provide a dimension-uniform positive-and-affine correction.

Likewise, averaging over each cyclic root subgroup separately produces
positive kernels on the individual root charts, but simultaneous invariance
under all root subgroups is already invariance under the group they generate.
That simultaneous kernel is exactly the positive-definite/ucp lift being
sought.  Thus neither the fixed centrality words nor root-subgroup averaging
proves `maslov-sector-tracial-generator-ucp-liftability` without one new
arithmetic positive-kernel estimate.

The detailed calculation and operator-system fence are in
`fixed-chevalley-prefix-gram-ucp-fence-proof`.

