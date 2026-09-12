---
rg: 2
id: elliptic-stabilizer-tree-transfer-obstruction-proof
kind: route
title: Discrete torsion-free subgroups meet elliptic stabilizers trivially, so they sit discretely in the tree group
target: tree-action-with-elliptic-stabilizers-kills-lattice-transfer
requires:
  - tree-by-elliptic-lattices-satisfy-strong-atiyah
  - free-cocompact-lattices-proportional-l2-betti
artifacts:
  - research/artifacts/atiyah-lattice-complex-2026-09-12.md
---

Derivation, in the notation of the claim.

1. **Trivial stabilizers.** Let `F ⊆ Γ_v = Γ ∩ H_v` be finite. By hypothesis `F` lies in a
   compact subgroup `K ≤ Aut(X)`. Then `⟨F⟩ ≤ Γ ∩ K`, which is discrete and compact, hence
   finite. So `Γ_v` is locally finite, and since `Γ` is torsion-free, `Γ_v = 1`.
2. **No inversions.** If `γ ∈ Γ` swaps the endpoints of an edge, `γ²` fixes a vertex. So
   `γ² = 1` by step 1, hence `γ = 1`.
3. **Discrete faithful image.** The kernel of `Γ → Aut(T)` fixes every vertex, so it is
   trivial by step 1. The image meets every vertex stabilizer of `Aut(T)` trivially. Those
   stabilizers are open, so the image is discrete; it is torsion-free because `Γ` is.
4. **Strong Atiyah.** Apply `tree-by-elliptic-lattices-satisfy-strong-atiyah` with
   `H_1 = N = 1` and `H_2 = Aut(T)`. The trivial group is locally elliptic and `H_1/N` is
   torsion-free abelian. The image of `Γ` is a discrete torsion-free subgroup of `H_1 × H_2`
   and is isomorphic to `Γ`, so `Γ` satisfies Strong Atiyah over `K`.
5. **Rationality.** With orbit representatives oriented, the combinatorial Laplacian `Δ_k`
   of `X` is a matrix over `Z[Γ]`. So `b_k^(2)(X;Γ) = dim_(N(Γ)) ker Δ_k` is an integer by
   step 4. By `free-cocompact-lattices-proportional-l2-betti`, every discrete `G` acting
   freely on simplices and cocompactly has `b_k^(2)(X;G) = r^(-1) b_k^(2)(X;Γ)` with
   `r ∈ Q_(>0)`, which is rational. ∎

Full write-up with remarks: `research/artifacts/atiyah-lattice-complex-2026-09-12.md`.
