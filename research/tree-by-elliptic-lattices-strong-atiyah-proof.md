---
rg: 2
id: tree-by-elliptic-lattices-strong-atiyah-proof
kind: route
title: Finitely generated kernel subgroups project injectively and discretely to the tree, hence are free
target: tree-by-elliptic-lattices-satisfy-strong-atiyah
requires:
  - atiyah-passes-to-torsion-free-elementary-amenable-extensions
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

Derivation. Write `π_1, π_2` for the coordinate projections.

1. **Quotient.** `Γ^0 = Γ ∩ (N × H_2)` is the kernel of `Γ → H_1/N`, so it is normal
   and `Γ/Γ^0` embeds in the torsion-free abelian group `H_1/N`.
2. **Compact first coordinates.** Let `F ≤ Γ^0` be finitely generated. The first
   coordinates of its generators lie in `N`, hence in a compact subgroup `K ≤ H_1`.
   So `F ≤ K × H_2`.
3. **Injective projection.** `ker(π_2|_F) ≤ Γ ∩ (K × 1)` is compact and discrete,
   hence finite, hence trivial because `Γ` is torsion-free.
4. **Discrete projection.** For a compact open `V ≤ H_2`,
   `π_2(F) ∩ V = π_2(F ∩ (K × V))`. That set is finite, since `K × V` is compact and
   `Γ` is discrete. So `π_2(F) ≅ F` is discrete in `H_2`.
5. **Freeness.**
   - Vertex stabilizers of `π_2(F)` are compact and discrete, hence finite, hence
     trivial.
   - An inversion `g` would give `g²` fixing the endpoints of an edge, so `g² = 1` and
     `g = 1`.
   - So `F` acts freely without inversions on `T` and is free (Serre, *Trees*, I.3.3).
   - If `H_2 = 1`, step 3 gives `F = 1`.
6. **Kernel satisfies Strong Atiyah.** `Γ^0` is a directed union of free groups, so it is
   locally indicable. Strong Atiyah holds for locally indicable groups: Fisher–Ng,
   arXiv:2606.19606 §1.1, quoted verbatim on `elementary-amenable-strong-atiyah-citation`,
   "all locally indicable groups [30]". Alternatively, free groups satisfy it (Linnell,
   Forum Math. 5 (1993)), and kernel dimensions of a matrix are computed over any
   subgroup containing its support.
7. **Extension.** `Γ/Γ^0` is torsion-free elementary amenable, so
   `atiyah-passes-to-torsion-free-elementary-amenable-extensions` (Schick, Corollary 3.2)
   gives Strong Atiyah for `Γ` over `K` closed under complex conjugation. ∎
