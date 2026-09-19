---
rg: 2
id: hyperbolic-lattice-rigid-measures-tight-proof
kind: route
title: "Orient every hyperplane slab by the free side of its extensions; consistent orientations give a boundary point or a finite centre, and an invariant measure allows neither"
target: hyperbolic-lattice-rigid-measures-are-hyperplane-tight
requires:
  - quantum-rigid-subshifts-are-determined-by-thick-collars
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
---

Lane proof by bh-ra-proof, 2026-09-19. Not independently reviewed. The argument is the `## Proof` section of
`hyperbolic-lattice-rigid-measures-are-hyperplane-tight`. It uses:
- one free side per thick cut (item 1 of the collars node) for the hyperplane slabs;
- Lemma 1 of the clustering node for consistency;
- the wire-net cost bound together with Abért–Nikolov for item 4(b).

The standard facts it uses are recalled, not re-read:
- visual-metric estimates in `ℍ^n`;
- the absence of invariant probability measures on `∂ℍ^n` for non-elementary groups;
- the fixed price of surface groups (Gaboriau).
