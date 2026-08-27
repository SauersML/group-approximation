---
rg: 2
id: atlas-charts-overlap-trivially-proof
kind: route
title: Exact prefix arithmetic for the intersection, Bass--Serre for the freeness
target: atlas-charts-overlap-trivially
requires: []
---

# Exact prefix arithmetic for the intersection, Bass–Serre for the freeness

**The computation.**  `experiments/atlas_relator_chart_overlap.py`
computes both 16-dimensional chart algebras by exact binary-Leavitt
arithmetic — expanding `δ_u δ_v^*` bases to a common per-degree
right-path depth and intersecting the resulting `F₂`-spans — obtaining
`dim(A₁ ∩ A₂) = 3` (the span of the three diagonal projections common to
both refinement patterns), and intersects the chart groups `K_i ⊆ A_i^×`
directly: the only common element is `1`.  Exact arithmetic over `F₂`,
no floats, seconds to reproduce.

**Freeness of the kernel.**  In a free product `K₁ * K₂`, a normal
subgroup meeting every conjugate of each factor trivially acts freely on
the Bass–Serre tree, hence is free (Nielsen–Schreier via the tree).  For
`R̄ = ker(P̄ ↠ Q)`: if `1 ≠ k ∈ K_i ∩ R̄^{g}`... equivalently the image
of `K_i` in `Q` is the chart copy of `A₈`, faithful by construction of
the atlas (the charts embed), so `K_i ∩ R̄ = 1`; conjugates likewise
since `R̄` is normal and the factor images remain faithful.  The
quotient graph of the tree action is the coset graph on
`Q/K₁ ⊔ Q/K₂` with edges `Q`, so `R̄ ≅ π₁` of that graph, free of
infinite rank; its shortest cycles correspond to the shortest kernel
words, the twenty radius-2 cross-chart commutators of syllable length 4.

**The amalgam consequence** is immediate: an amalgamated decomposition
along `K₁ ∩ K₂ = 1` is the free product itself, so no relator arises
from overlap identifications, and the uniform-refinement warning is the
rank-condition computation recorded in the notes file.

Finally, if `T ⊆ R̄`, normality of `R̄` gives
`<<T>>_(P̄) ⊆ R̄`.  Faithfulness of each chart gives
`R̄ ∩ K_i=1`, hence `<<T>>_(P̄) ∩ K_i=1`.  This proves the finite-packet
no-collapse consequence without a quotient computation.
