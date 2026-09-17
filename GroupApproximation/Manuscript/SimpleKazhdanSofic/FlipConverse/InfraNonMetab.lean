import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonMetabStatements
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonMetabPerm
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerBaseMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# Local non-metabelianity of `[[T]]`, part 3: the witnesses

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Infrastructure lane `sk-flip-05`.

For a minimal homeomorphism `T` of a Cantor space (compact, Hausdorff, totally disconnected,
perfect) and a nonempty open `W`, there are `a, b, c, d ∈ [[T]]` supported in `W` with
`⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1`, and there are `a, b ∈ [[T]]` supported in `W` with `a b ≠ b a`.

Route.

* Lane `sk-flip-03` (on disk, `exists_isClopen_tower_in_open`) gives a nonempty clopen `V` and
  exponents `k : Fin 5 → ℤ` with 5 pairwise disjoint levels `T^{k i} V ⊆ W`.
* Lane `sk-flip-04` (`TowerPermEmbeddingStatement`, not yet on disk) gives an injective
  `φ : S_5 →* [[T]]` supported in `⋃ T^{k i} V ⊆ W`
  (`exists_permEmbedding_supportedIn_of_towerPermEmbedding`).
* `φ` preserves commutators (`map_commutatorElement`) and reflects `1` (`map_ne_one_iff`), so the
  finite computations of `InfraNonMetabPerm` transfer.

The endpoints are `_of_towerPermEmbedding` reductions; `TowerPermEmbeddingStatement` is TRUE
(proof sketch in `InfraNonMetabStatements`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open scoped commutatorElement

universe u

/-- A tower with `n` levels inside `W` embeds `S_n` into `[[T]]` with support in `W`. -/
theorem exists_permEmbedding_supportedIn_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{u}) {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) (n : ℕ) :
    ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
      ∀ σ : Equiv.Perm (Fin n), SupportedIn (φ σ : X ≃ₜ X) W := by
  obtain ⟨V, k, -, hV, hVne, hsub, hdisj⟩ := exists_isClopen_tower_in_open hT hW hne n
  obtain ⟨φ, hinj, hsupp⟩ := h04 X T V n k hV hVne hdisj
  exact ⟨φ, hinj, fun σ => (hsupp σ).mono (Set.iUnion_subset hsub)⟩

/-- Local non-metabelianity of `[[T]]` for a minimal homeomorphism of a Cantor space: every
nonempty open `W` supports `a, b, c, d ∈ [[T]]` with `⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1`. -/
theorem exists_nonMetabelian_supportedIn_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{u}) {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b c d : topologicalFullGroup T,
      SupportedIn (a : X ≃ₜ X) W ∧ SupportedIn (b : X ≃ₜ X) W ∧
        SupportedIn (c : X ≃ₜ X) W ∧ SupportedIn (d : X ≃ₜ X) W ∧ ⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1 := by
  obtain ⟨φ, hinj, hsupp⟩ :=
    exists_permEmbedding_supportedIn_of_towerPermEmbedding h04 hT hW hne 5
  refine ⟨φ (Equiv.swap 0 1), φ (Equiv.swap 1 2), φ (Equiv.swap 2 3), φ (Equiv.swap 3 4),
    hsupp _, hsupp _, hsupp _, hsupp _, ?_⟩
  have h := (map_ne_one_iff φ hinj).2 perm_fin_five_commutator_commutator_ne_one
  simpa only [map_commutatorElement] using h

/-- For a minimal homeomorphism of a Cantor space, every nonempty open `W` supports two
non-commuting elements of `[[T]]`. -/
theorem exists_not_commute_supportedIn_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{u}) {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b : topologicalFullGroup T,
      SupportedIn (a : X ≃ₜ X) W ∧ SupportedIn (b : X ≃ₜ X) W ∧ a * b ≠ b * a := by
  obtain ⟨φ, hinj, hsupp⟩ :=
    exists_permEmbedding_supportedIn_of_towerPermEmbedding h04 hT hW hne 5
  refine ⟨φ (Equiv.swap 0 1), φ (Equiv.swap 1 2), hsupp _, hsupp _, fun h => ?_⟩
  have h' : φ (Equiv.swap 0 1 * Equiv.swap 1 2) = φ (Equiv.swap 1 2 * Equiv.swap 0 1) := by
    rw [map_mul, map_mul]
    exact h
  exact perm_fin_five_swap_mul_ne (hinj h')

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_permEmbedding_supportedIn_of_towerPermEmbedding
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_nonMetabelian_supportedIn_of_towerPermEmbedding
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_not_commute_supportedIn_of_towerPermEmbedding
