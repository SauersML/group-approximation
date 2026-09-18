---
rg: 2
id: artin-hub-cones-reduce-pbh-to-coned-cliques-proof
kind: route
title: Split the hub cone along the folded star of any vertex whose star is not everything, folding the vertex and all non-neighbours onto the hub, and induct down to coned cliques
target: artin-hub-cones-reduce-pbh-to-coned-cliques
requires:
  - artin-pbh-reduces-along-folding-separators
  - artin-ordinary-foldings-are-retractions
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation of the target. Write `Γ' = Γ^k`.

**1. Parabolic embedding.** For any Artin group `A_Σ` and any vertex subset `S`, the natural map `A_(Σ[S]) → A_Σ` is injective (van der Lek, thesis, Nijmegen 1983; stated as Theorem 5.4 of L. Paris, arXiv:1211.7339, as read in `research/artifacts/zp-artin-direct-f-infinity-2026-09-13.md`). Apply it with `Σ = Γ'`, `S = V(Γ)`: `Γ'[V(Γ)] = Γ`.

**2. One splitting step.** Let `Π ⊆ V(Γ)` induce a subgraph `Δ = Γ[Π]` and consider `Δ' = Γ'[Π ∪ {e}]`, the hub cone of `Δ` (the hub labelling restricts). Suppose some `v ∈ Π` has star `st_Δ(v) = {v} ∪ N_Δ(v)` different from `Π`. Put

    Λ = N_Δ(v) ∪ {e},   V_1 = st_Δ(v) ∪ {e},   V_2 = (Π \ {v}) ∪ {e}.

- `V_1 ∩ V_2 = Λ` and `V_1 ∪ V_2 = Π ∪ {e}`.
- `V_1 \ Λ = {v}` and `V_2 \ Λ = Π \ st_Δ(v)` is nonempty. No edge joins them, since every neighbour of `v` in `Δ` lies in `Λ`, and `e ∈ Λ`.
- **Folding of `Δ'[V_1]` onto `Λ`:** `v ↦ e`, identity on `Λ`. An edge `vw` with `w ∈ N_Δ(v)` goes to `(e, w)`; `e` and `w` are distinct, adjacent in `Δ'[Λ]` with label `k_w`, and `k_w | m_vw` by the hub condition: case (c) of `artin-ordinary-foldings-are-retractions`. The edge `ve` goes to `(e, e)`: case (a). Edges inside `Λ` are fixed.
- **Folding of `Δ'[V_2]` onto `Λ`:** `u ↦ e` for every `u ∈ Π \ st_Δ(v)`, identity on `Λ`. An edge `uw` with `w ∈ N_Δ(v)` goes to `(e, w)`, with `k_w | m_uw`: case (c). An edge `uu'` with both ends outside `st_Δ(v)`, or an edge `ue`, goes to `(e, e)`: case (a).
- So Part 1 of `artin-pbh-reduces-along-folding-separators` gives `A_(Δ') = A_(Δ'[V_1]) *_(A_Λ) A_(Δ'[V_2])`, and `A_(Δ') ∈ B_A` iff `A_(Δ'[V_1]) ∈ B_A` and `A_(Δ'[V_2]) ∈ B_A`.
- `Δ'[V_1]` is the hub cone of `Γ[st_Δ(v)]` and `Δ'[V_2]` is the hub cone of `Γ[Π \ {v}]`. Both vertex sets are proper subsets of `Π`.

**3. Induction.** Induct on `|Π|`. If `Δ` is a clique there is nothing to do. Otherwise some `v ∈ Π` has `st_Δ(v) ≠ Π`, and step 2 reduces `A_(Δ') ∈ B_A` to the same statement for the hub cones of two proper subsets. The recursion ends at vertex sets in which every star is the whole set, i.e. at cliques `Ψ` of `Γ`. Each such `Ψ` lies in a maximal clique `Ψ_0`, and `Ψ^k` is an induced subgraph of `Ψ_0^k`, so `A_(Ψ^k) ≤ A_(Ψ_0^k)` by step 1; `B_A` is closed under subgroups. So if every `A_(Ψ_0^k) ∈ B_A`, then `A_(Γ') ∈ B_A`. Conversely each `Ψ_0^k` is an induced subgraph of `Γ'`, so `A_(Ψ_0^k) ≤ A_(Γ')`. Taking `Π = V(Γ)` gives Part 2.

**4. Part 3.** Combine Parts 1 and 2 with closure of `B_A` under subgroups (`boone-higman-type-a-class-closed-under-finite-extensions`) and `type-a-action-gives-boone-higman-for-subgroups`.

**5. Calibration (even case).** With `k ≡ 2`, the hub `e` commutes with every vertex, `A_(Γ') = A_Γ × Z`, and every `Δ^k` is `A_Δ × Z`. The statement then says `A_Γ × Z ∈ B_A` iff every `A_Δ × Z ∈ B_A`; for even `Γ` this is the known clique reduction (`artin-pbh-reduces-to-odd-component-cliques`, Corollary C), as it should be.

**6. Bounded priority check (2026-09-18).** The folding and retraction searches recorded in `artin-pbh-reduces-along-folding-separators-proof` (arXiv API; arXiv:2603.15314, 2408.12291, 2407.07459, 2204.05142), the Boone--Higman literature survey `research/artifacts/gq-bh-bh-lit-survey.md`, and Huang--Jankiewicz--Przytycki's cubulation criterion (quoted in `research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md`, §8). None uses a hub cone for Boone--Higman. MathSciNet was not searched.

QED
