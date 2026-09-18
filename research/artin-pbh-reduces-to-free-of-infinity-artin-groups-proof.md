---
rg: 2
id: artin-pbh-reduces-to-free-of-infinity-artin-groups-proof
kind: route
title: Split the clone double along each original non-edge u|w, folding u onto its clone û and w onto ŵ, until the pieces are complete
target: artin-pbh-reduces-to-free-of-infinity-artin-groups
requires:
  - artin-pbh-reduces-along-folding-separators
  - artin-ordinary-foldings-are-retractions
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Notation of the target; write `Γ' = Γ^(L,M)`.

**1. Parabolic embedding.** Standard parabolic subgroups of any Artin group embed (van der Lek, thesis 1983; L. Paris, arXiv:1211.7339, Theorem 5.4, as read in `research/artifacts/zp-artin-direct-f-infinity-2026-09-13.md`), and `Γ'[V] = Γ`. This is Part 1.

**2. The splitting step.** Let `V̂ ⊆ S ⊆ V ⊔ V̂`. The non-edges of `Γ'[S]` are the pairs `u, w ∈ S ∩ V` with `m_uw = ∞`, since every pair involving a clone has a finite label. Suppose `u, w ∈ S ∩ V` is such a pair. Put `Λ = S \ {u, w}`, `V_1 = S \ {w}`, `V_2 = S \ {u}`. Then `V_1 ∩ V_2 = Λ`, `V_1 \ Λ = {u}`, `V_2 \ Λ = {w}`, and `u, w` are not adjacent.
- **Folding `u ↦ û` on `Γ'[V_1]`.** `û ∈ Λ`. Every edge at `u` inside `V_1` goes to `Λ`:
  - `u û` goes to `(û, û)`: case (a) of `artin-ordinary-foldings-are-retractions`;
  - `u y` with `y ∈ V`, `m_uy < ∞`, goes to `(û, y)`, adjacent in `Γ'[Λ]` with label `m(û, y) = m_uy`, which divides `m_uy`: case (c);
  - `u x̂` with `x ≠ u` goes to `(û, x̂)`, with label `m(û, x̂) = m(u, x̂)`: case (c).
  Edges inside `Λ` are fixed.
- **Folding `w ↦ ŵ` on `Γ'[V_2]`**: the same.
- Part 1 of `artin-pbh-reduces-along-folding-separators` gives `A(Γ'[S]) = A(Γ'[V_1]) *_(A(Γ'[Λ])) A(Γ'[V_2])`, and `A(Γ'[S]) ∈ B_A` iff `A(Γ'[V_1]) ∈ B_A` and `A(Γ'[V_2]) ∈ B_A`.
- `V_1` and `V_2` both contain `V̂`, and each has fewer non-edges than `S` (the pair `u, w` is gone).

**3. Induction and Part 2.** Induct on the number of non-edges of `Γ'[S]`, starting from `S = V ⊔ V̂`. The process ends at sets `S` with `S ∩ V` a clique of `Γ`; then `Γ'[S]` is complete and is an induced subgraph of `Γ'[Δ ∪ V̂]` for a maximal clique `Δ ⊇ S ∩ V`, so `A(Γ'[S]) ≤ A(Γ'[Δ ∪ V̂])` by step 1. `B_A` is closed under subgroups (`boone-higman-type-a-class-closed-under-finite-extensions`). So if every `A(Γ'[Δ ∪ V̂]) ∈ B_A`, then `A_(Γ') ∈ B_A`. Conversely each `Γ'[Δ ∪ V̂]` is induced in `Γ'`, so its Artin group is a subgroup of `A_(Γ')`.

**4. Part 3.** *If.* Given any `Γ`, take `L = M = 2`. Every piece `Γ'[Δ ∪ V̂]` is complete, so by hypothesis its Artin group is in `B_A`; by Part 2, `A_(Γ') ∈ B_A`, and by Part 1 and closure under subgroups, `A_Γ ∈ B_A`. *Only if.* A complete defining graph is a special case.

**5. Calibration.** For a right-angled Artin group (labels 2 and ∞) with `L = M = 2`, every piece is the free abelian group `Z^(|V| + |Δ|)`, which is in `B_A`; so is every right-angled Artin group (survey Theorem 5.1(3)), as it should be.

**6. Why the clones are needed.** For `m_uw = ∞` the standard splitting `A_Γ = A_(V\w) *_(A_(V\{u,w})) A_(V\u)` has amalgamated subgroup that is usually not a retract of either side (for the all-3 four-cycle see `triangle-free-all-3-artin-groups-satisfy-pbh`), so `pbh-class-closed-under-common-retract-amalgams` does not apply. The clone `û` has the same labels as `u` to every vertex of the separator, so it absorbs `u` in a folding, and the same splitting becomes one over a common retract.

QED
