---
rg: 2
id: non-ascending-one-cell-complements-have-vanishing-l2-b1
kind: claim
title: A one-cell complement whose group is not an ascending HNN extension of a finitely generated group has vanishing first L²-Betti number
distinct_from:
  ascending-hnn-one-cell-complements-have-vanishing-l2-b1: that is the proved case, where the group is an ascending HNN extension of a finitely generated group; this is the remaining case.
  one-cell-complement-groups-have-vanishing-first-l2-betti: that is the full statement for every one-cell complement; this is its residual half.
  l2-normal-rank-bound-fails-for-torsion-free-groups: that refutes the torsion-free Osin--Thom bound with groups that are not finitely generated; the groups here are finitely presented, which those counterexamples are not.
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

**OPEN.** Let `L` be a finite connected contractible 2-complex, `e` an open 2-cell, `K = L − e` and
`G = π₁(K)`. If `G` is not isomorphic to `H *_σ` for any finitely generated group `H` and injective
endomorphism `σ`, then `b₁^(2)(G) = 0`.

With `ascending-hnn-one-cell-complements-have-vanishing-l2-b1`, this is exactly
`one-cell-complement-groups-have-vanishing-first-l2-betti`, through the route
`one-cell-l2-vanishing-via-ascending-dichotomy`. So it carries that claim's consequences:
- Whitehead's finite one-cell case;
- asphericity of every labelled oriented tree complex;
- the balanced killing form of Kervaire--Laudenbach.

## Shape of the residual groups

- By `bieri-strebel-splitting-over-kernel-of-map-to-z`, `G` is an HNN extension `HNN(H, K₀, L₀, θ)`
  with finitely generated base `H ≤ [G, G]`. Here neither associated subgroup is all of `H`.
  Britton's lemma then gives a non-abelian free subgroup; that step is recalled, not pinned.
- The residual class contains the group of every non-fibred knot. This is recalled, not pinned:
  Wirtinger presentations are LOT presentations, and a knot group is ascending over a finitely
  generated base only when the knot is fibred. There `b₁^(2) = 0` holds for 3-manifold reasons
  (Lott--Lück, recalled). So vanishing in the residual class can hold for geometric reasons that
  no HNN-splitting argument sees.

## Attempts

1. **Normal-subgroup vanishing theorems. Does not apply.** Items (vi) and (vii) of Theorem 6.4 in
   Lück's survey (`arXiv:math/0310489`; TeX l.3467–3477, read on MSI 2026-09-14) need an infinite
   normal subgroup with finite first L²-Betti number. The quotient must contain an element of
   infinite order or finite subgroups of arbitrarily large order for (vi), and must be infinite
   countable for (vii). The kernel `[G, G]` is
   not finitely generated here. The finiteness hypothesis is genuinely needed: in `F₂`, the quotient
   by `[F₂, F₂]` is `Z²`, yet `b₁^(2)(F₂) = 1`. So item (vi) forces `b₁^(2)([F₂, F₂]) = ∞`.
2. **Cyclic-cover approximation. Computes the wrong invariant.** The subgroups `φ⁻¹(nZ)` intersect
   in `[G, G]`, not in `1`, so Lück approximation along them does not compute `b₁^(2)(G)`.
   `one-cell-complement-cyclic-cover-homology-is-finite` shows the cyclic-cover data is always tame:
   `H₁(K_∞; F)` is finite-dimensional and `H₂(K_∞) = 0`.
3. **Cyclic-cover homology. Cannot decide.** The same node gives a finite 2-complex with χ = 0,
   `H₁ = Z`, `H₂ = 0`, the same rational cyclic-cover homology, and `b₁^(2) > 0`. Any proof must use
   the weight-one or contractible-completion property, which is a Kervaire-type input.
4. **Osin--Thom limits. Partial.** `lo-amenable-limit-one-cell-complements-are-aspherical` settles
   groups that are limits of left-orderable amenable groups. This lane does not know whether that
   class meets the residual one.

## Exact gap

Finitely presented weight-one groups `G` with `G^ab ≅ Z` and a finite 2-complex `K` with χ = 0 that
becomes contractible after one 2-cell is attached, such that no Bieri--Strebel splitting along
`G → Z` is ascending. For these, no vanishing mechanism for `b₁^(2)` is known to this lane.
