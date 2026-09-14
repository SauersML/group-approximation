---
rg: 2
id: lot-at-most-six-vertices-census-proof
kind: route
title: Reduce to reduced trees with at most six vertices, enumerate them all, and certify each by injectivity or by the one-cycle local indicability criterion
target: lot-complexes-with-at-most-six-vertices-are-aspherical
requires: []
artifacts:
  - research/artifacts/hl-whitehead-lot-certify-2026-09-14.md
---

Notation as in the claim.

## 1. Reduction

Harlander--Rosebrock, arXiv:1212.1943v6, Section 1, define a LOT as reduced when it is compressed
(no edge is labelled by one of its own vertices), boundary reduced and interior reduced. They
record: "Howie [7] observed that a labeled oriented tree G can be transformed into a reduced
labeled oriented tree G_red so that K(G) and K(G_red) have the same homotopy type." Each move is a
3-deformation and deletes a vertex.

So it suffices to treat reduced LOTs with at most six vertices.
- A one-vertex LOT gives a circle, which is aspherical.
- No reduced LOT has exactly two vertices, since its only edge would have to be labelled by one of
  its endpoints.

## 2. Two sufficient criteria

**(inj)** "Theorem 1.1 Injective labeled oriented trees are aspherical" (loc. cit.). A LOT is
injective when no vertex labels two edges.

**(IT)** Barreto--Minian, arXiv:2308.07447v1:
- Corollary 3.1: "Let Γ be a LOT. If either I(Γ) or T(Γ) has at most one cycle, then G(Γ) is
  locally indicable."
- Here T(Γ) has an edge {λ(e), i(e)} and I(Γ) has an edge {λ(e), t(e)} for each edge e.
- Their introduction also records that "any connected 2-complex X with π1(X) locally indicable and
  H2(X) = 0 is aspherical".

H₂(K(Γ)) = 0 holds for every LOT with n vertices:
1. K(Γ) has one 0-cell, n 1-cells and n − 1 2-cells, so χ = 0.
2. H₁ = Z^n / ⟨e_{i(e)} − e_{t(e)}⟩ ≅ Z, because the tree is connected.
3. H₂ is the kernel of the cellular boundary map from Z^{n−1}, so it is free, of rank
   χ − 1 + rank H₁ = 0.

So (IT) implies asphericity.

## 3. Exhaustive census

**Code.** `experiments/lot-asphericity-census/census_primary.py` with `lot_primary.py`.

**Enumeration.** For each free tree shape on n vertices (n = 3, 4, 5, 6), the census takes:
- all orientations with the first edge fixed. Reversing every edge only reorients each 1-cell,
  since x ↦ x⁻¹ carries i λ t⁻¹ λ⁻¹ to a cyclic permutation of the reversed edge's relator
  t λ i⁻¹ λ⁻¹.
- all compressed labellings.
- only the boundary-reduced and interior-reduced ones.

This covers every reduced LOT with n vertices up to isomorphism. Classes are counted up to shape
automorphisms and global reversal, and each class is tested.

**Results.** Every class passes (inj) or (IT), and nothing survives.

| n | classes | (inj) | (IT) | survivors |
|---|---|---|---|---|
| 3 | 2 | 2 | 0 | 0 |
| 4 | 8 | 6 | 2 | 0 |
| 5 | 206 | 104 | 102 | 0 |
| 6 | 6234 | 1866 | 4368 | 0 |

**Checking.** Both criteria are elementary to re-check: (inj) is a property of the label list, and
(IT) is the cyclomatic number of two graphs with n vertices and n − 1 edges.

**Runs.**
- n = 5, 6: tallies from MSI job 781699 (`census_primary.py`, all shapes).
- n = 3, 4: tallies from a login-node run with the same script.
- The data are in `experiments/lot-asphericity-census/outp34/` and `outp57/`.

**Calibration.** `controls.py` passes 17/17 and `controls2.py` 13/13 (artifact §2). The (IT)
implementation agrees with an independent Theorem 2.5 check on all 81 labellings of the
five-vertex path with a one-cycle graph.

Elementary beyond the two cited theorems and the reduction.
