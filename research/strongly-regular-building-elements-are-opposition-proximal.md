---
rg: 2
id: strongly-regular-building-elements-are-opposition-proximal
kind: claim
title: Strongly regular hyperbolic automorphisms of locally finite Euclidean buildings contract the chambers opposite their repelling chamber uniformly on compacta
distinct_from:
  opposition-ping-pong-criterion-gives-mixed-identity-freeness: that is an abstract ping-pong criterion on any compact space with an opposition relation; this is the geometric input saying that strongly regular elements of Euclidean buildings are proximal in its sense.
---

**OPEN.** Let `X` be a locally finite thick Euclidean building. Let
`Z = Ch(∂X)` be the set of chambers at infinity with the cone topology, and let
`O ⊆ Z × Z` be the opposition relation. The claim has two parts.

- **(a)** `Z` is compact Hausdorff, `O` is open, and `O(c)` is dense in `Z`
  for every `c`.
- **(b)** Take a type-preserving strongly regular hyperbolic automorphism `a` of
  `X`, with translation apartment `A`. Let `c₊, c₋ ∈ Ch(∂A)` be the chambers
  containing the attracting and repelling endpoints of its axes. Then `a` is
  proximal with poles `(c₊, c₋)` in the sense of
  `opposition-ping-pong-criterion-gives-mixed-identity-freeness`.

## Attempts

1. **Pointwise version (literature).** Caprace--Ciobotaru, arXiv:1304.6210v2,
   Proposition 2.10 (pinned in the artifact of lane solve-titz-witzel-mif):
   for every `ξ ∈ ∂X`, `lim aⁿ(ξ)` exists in the cone topology and equals
   `ρ_{A,c₋}(ξ)`.
   - **What that gives.** Their retraction `ρ_{A,c₋}` restricts to an
     isomorphism onto `A` of every apartment containing `c₋`. Isomorphisms
     preserve opposition, so a chamber opposite `c₋` goes to `c₊`. So `aⁿ`
     converges pointwise to `c₊` on the points of chambers opposite `c₋`.
   - **What's missing.** Uniformity on compact subsets of `O(c₋)`, which is
     (PR2).
2. **Sketch of uniformity, not written as a proof.**
   - **Exhaustion.** Fix a special vertex `v ∈ A`. Put `d ∈ O_R(c₋)` when some
     apartment containing `c₋` and `d` meets `A` in a sector `S_{c₋}(y)` with
     `y` a special vertex and `|v − y| < R`.
   - **Openness.** It should follow from the lemma that two sectors based at a
     special vertex with opposite germs lie in a common apartment. That needs
     a base-point change for sector neighbourhoods; neither is pinned here.
   - **Contraction.** `a` translates `A` by a regular vector pointing into
     `c₊`, so `S_{c₋}(y + nτ)` contains any fixed ball of `A` around `v` for
     `n ≥ n(R)`. The isomorphism between the two apartments that fixes their
     intersection then forces the sector from `v` to `aⁿ(d)` to agree with
     `S_{c₊}(v)` on that ball.
   - **Compactness.** A compact `K ⊆ O(c₋)` lies in one `O_R(c₋)`.
   - Part (a) was not attempted.
