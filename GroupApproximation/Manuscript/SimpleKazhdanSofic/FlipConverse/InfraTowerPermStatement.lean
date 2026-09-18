import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerPerm
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonMetabBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 4: discharging `TowerPermEmbeddingStatement`

Infrastructure for census row `2e7c7d9ab149` (the key is absent from the current tex, so there
is no line number).  Lane sk-flip-04.

Lane sk-flip-05 states this lane's result as `TowerPermEmbeddingStatement` (general exponents
`k : Fin n → ℤ`).  `towerPermEmbeddingStatement_holds` proves it from `towerPerm`,
`towerPerm_injective` and `towerPerm_supportedIn`.  Plugging it into the `_of_towerPermEmbedding`
endpoints of lane sk-flip-05 gives their unconditional forms.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open scoped commutatorElement

universe u

/-- The lane sk-flip-04 interface used by lane sk-flip-05 holds. -/
theorem towerPermEmbeddingStatement_holds : TowerPermEmbeddingStatement.{u} := by
  intro X _ T V n k hV hne hdisj
  exact ⟨towerPerm T V k hV hdisj, towerPerm_injective T V k hV hdisj hne,
    towerPerm_supportedIn T V k hV hdisj⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPermEmbeddingStatement_holds

/-- For a minimal homeomorphism of a Cantor space, every nonempty open `W` carries an embedding
`Sym(n) ↪ [[T]]` supported in `W`. -/
theorem exists_permEmbedding_supportedIn {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) (n : ℕ) :
    ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
      ∀ σ : Equiv.Perm (Fin n), SupportedIn (φ σ : X ≃ₜ X) W :=
  exists_permEmbedding_supportedIn_of_towerPermEmbedding towerPermEmbeddingStatement_holds hT hW
    hne n

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_permEmbedding_supportedIn

/-- Local non-metabelianity of `[[T]]` for a minimal homeomorphism of a Cantor space. -/
theorem exists_nonMetabelian_supportedIn {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b c d : topologicalFullGroup T,
      SupportedIn (a : X ≃ₜ X) W ∧ SupportedIn (b : X ≃ₜ X) W ∧
        SupportedIn (c : X ≃ₜ X) W ∧ SupportedIn (d : X ≃ₜ X) W ∧ ⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1 :=
  exists_nonMetabelian_supportedIn_of_towerPermEmbedding towerPermEmbeddingStatement_holds hT hW
    hne

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_nonMetabelian_supportedIn

/-- Every nonempty open `W` supports two non-commuting elements of `[[T]]`. -/
theorem exists_not_commute_supportedIn {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b : topologicalFullGroup T,
      SupportedIn (a : X ≃ₜ X) W ∧ SupportedIn (b : X ≃ₜ X) W ∧ a * b ≠ b * a :=
  exists_not_commute_supportedIn_of_towerPermEmbedding towerPermEmbeddingStatement_holds hT hW
    hne

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_not_commute_supportedIn

/-- The lane sk-flip-07 interface `NonDisjWitNonMetabelianStatement` holds. -/
theorem nonDisjWitNonMetabelianStatement_holds : NonDisjWitNonMetabelianStatement :=
  nonDisjWitNonMetabelian_of_towerPermEmbedding towerPermEmbeddingStatement_holds

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.nonDisjWitNonMetabelianStatement_holds

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
