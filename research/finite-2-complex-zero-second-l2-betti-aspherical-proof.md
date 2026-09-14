---
rg: 2
id: finite-2-complex-zero-second-l2-betti-aspherical-proof
kind: route
title: Integral 2-cycles of the universal cover lie in a zero ℓ²-kernel
target: finite-2-complex-with-zero-second-l2-betti-is-aspherical
requires: []
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Notation: K is a finite connected 2-complex, G = π₁(K) infinite, c_i the number
of i-cells, and K̃ the universal cover with its free cocompact G-action.

1. **Chain complexes.** The cellular chain complex of K̃ is
   0 → ZG^{c₂} --∂₂--> ZG^{c₁} --∂₁--> ZG^{c₀} → 0, where each ∂_i is right
   multiplication by a matrix over ZG. The ℓ²-chain complex uses the same
   matrices on ℓ²(G)^{c_i}.
2. **Euler--Poincaré.** χ(K) = b₀^(2) − b₁^(2) + b₂^(2) for the L²-Betti numbers of
   K̃ (Lück, *L²-Invariants*, Theorem 1.35(2); survey pin below).
3. **Degree 0.** b₀^(2) = 0 because G is infinite (Lück, Theorem 1.35(8)). Directly:
   - The orthogonal complement of the closure of im ∂₁^(2) is ker of the adjoint of ∂₁^(2).
   - That adjoint sends an ℓ² function f on the vertices of K̃ to the edge function
     f(τ) − f(ι).
   - Its kernel consists of functions that are constant along edges. K̃ is connected, so
     they are constant, and a constant ℓ² function on the infinite vertex set is 0.
4. **Degree 1.** K̃ is simply connected, so it is the 2-skeleton of a model of EG
   obtained by attaching free G-cells of dimension at least 3.
   - Lück defines b_p^(2)(G) := b_p^(2)(EG, N(G)).
   - The inclusion f: K̃ → EG is C-homologically 2-connected: bijective on H₀ and H₁,
     and surjective on H₂ because H₂(EG) = 0. For H ≠ 1 both fixed sets are empty,
     since the actions are free.
   - Homology invariance for n = 2 then gives b₁^(2)(K̃) = b₁^(2)(EG) = b₁^(2)(G).
5. **Degree 2.** There are no 3-cells, so the reduced second ℓ²-homology is
   ker(∂₂^(2)) itself, a closed G-invariant subspace of ℓ²(G)^{c₂}. Its von Neumann
   dimension is b₂^(2) (comparison pin below), and by steps 2–4 this is
   χ(K) + b₁^(2)(G) = 0.
6. **Faithfulness.** A closed G-invariant subspace V of ℓ²(G)^{c₂} with von Neumann
   dimension 0 is zero.
   - Let P be the orthogonal projection onto V, and δ_j the vector δ_e in coordinate j.
   - P commutes with G, and dim V = Σ_j ⟨Pδ_j, δ_j⟩ = Σ_j ‖Pδ_j‖².
   - If this is 0, then P(gδ_j) = gPδ_j = 0 for all g and j. These vectors span a dense
     subspace, so P = 0.

   So ker(∂₂^(2)) = 0.
7. **Integral cycles.** ZG^{c₂} ⊂ ℓ²(G)^{c₂} as finitely supported vectors, and ∂₂
   acts on both by the same matrix. So H₂(K̃; Z) = ker(∂₂ on ZG^{c₂}) ⊆ ker(∂₂^(2)) = 0.
8. **Asphericity.** K̃ is simply connected and 2-dimensional with H₂(K̃) = 0, and
   H_i(K̃) = 0 for i ≥ 3 by dimension. By Hurewicz and Whitehead, K̃ is
   contractible, so π₂(K) = π₂(K̃) = 0 and K is aspherical.

**Sources.** W. Lück, *L²-Invariants from the Algebraic Point of View*, arXiv:math/0310489.
The e-print TeX `ltwoalg.tex` was read on MSI on 2026-09-14
(`/scratch.global/sauer354/ideas-topology/src/luck/`). Statements are verbatim up to macros.

- **Groups** (Definition "L²-Betti numbers of groups", l.1176–1182):
  b_p^(2)(G) := b_p^(2)(EG, N(G)).
- **Cellular chains** (Lemma `lem: singular = cellular`, l.1292–1297): for a G-CW complex X,
  b_p^(2)(X; N(G)) = dim_{N(G)}(H_p(N(G) ⊗_{ZG} C_*^c(X))).
- **Theorem "L²-Betti numbers for arbitrary spaces"** (l.1315ff). Its proof is referred to
  Lück's book, Theorems 1.35 and 6.54.
  - *Homology invariance* (l.1321–1344), used in step 4. If f: X → Y is a G-map such that
    f^H is C-homologically n-connected for every subgroup H ⊆ G (bijective on H_p for
    p < n, surjective for p = n), then b_p^(2)(X) = b_p^(2)(Y) for p < n.
  - *Zero-th L²-Betti number* (l.1437–1450), used in step 3, which is also proved inline.
    For a path-connected G-space X, b₀^(2)(X; N(G)) = |G|⁻¹, "defined to be zero if the
    order |G| of G is infinite".
  - *Euler--Poincaré formula* (l.1456–1475), used in step 2. For a free finite G-CW complex
    X, χ(G\X) = Σ_p (−1)^p b_p^(2)(X).
- **Comparison with reduced ℓ²-homology** (l.1669–1695), used in step 5.
  - For a cocompact free G-CW complex X, C_*^(2)(X) := C_*^c(X) ⊗_{ZG} l²(G), and
    H_p^(2)(X; l²(G)) = ker(c_p^(2)) / closure(im c_{p+1}^(2)).
  - Then b_p^(2)(K; N(G)) = dim_{N(G)}(H_p^(2)(K; l²(G))), citing Lück 1997, Theorem 6.1.

**Trust surface.**
- Steps 3 and 6 are proved inline.
- Steps 2, 4 and 5 use the pinned statements. Their proofs are references in the survey
  to Lück's book and to Lück 1997, and were not re-derived.
- The survey writes the comparison for an equivariant triangulation K of a manifold. It
  sets up the chain complex for any cocompact free G-CW complex, and the cited Theorem 6.1
  was not opened.
