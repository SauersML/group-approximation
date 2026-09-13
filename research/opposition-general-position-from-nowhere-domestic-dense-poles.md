---
rg: 2
id: opposition-general-position-from-nowhere-domestic-dense-poles
kind: claim
title: General position of poles follows from nowhere-dense domestic sets and dense pole pairs
distinct_from:
  opposition-ping-pong-criterion-gives-mixed-identity-freeness: that derives mixed-identity-freeness from the general position hypothesis (GP); this derives (GP) from two separate topological inputs, one about each group element and one about proximal elements.
---

Let `G` act by homeomorphisms on a compact Hausdorff space `Z`, and let
`O ⊆ Z × Z` be symmetric and open, with `O(z) = {y : (y, z) ∈ O}` dense in `Z`
for every `z`. "Proximal with poles `(z₊, z₋)`" and (GP) are as in
`opposition-ping-pong-criterion-gives-mixed-identity-freeness`. Suppose:

- **(D1)** for every `g ∈ G ∖ {1}`, the closed set
  `N(g) = {z ∈ Z : (g·z, z) ∉ O}` has empty interior;
- **(D2)** the pairs `(z₊, z₋)` of poles of proximal elements of `G` are dense
  in `O`.

Then (GP) holds, so `G` is mixed-identity-free.

Here `N(g)` is closed because its complement is the preimage of `O` under the
continuous map `z ↦ (g·z, z)`. Elementary; no novelty is claimed.

DERIVATION
opposition-general-position-density-proof
