import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Central images of self-commutator subgroups are trivial

Lane `sk-rows-16` (carto-sk-rows, section 4), group-theory core of the padded kill on Khanh's
route (arXiv:2609.08428v1, Theorem 5.4) to the rank-four `K₂` gap behind tex 733.  No single tex
sentence is formalized here.

## Statement

Let `φ : S →* T` be a group homomorphism and `N ≤ S` a subgroup with `N ≤ ⁅S, N⁆`.  If
`φ(N) ≤ Z(T)`, then `φ(N) = 1`.

## Truth check

`φ(N) ≤ φ⁅S, N⁆ = ⁅φ S, φ N⁆ ≤ ⁅T, Z(T)⁆ = 1`.  Small sanity model: `S = T = SL₂(𝔽₅)`,
`N = Z(S) = {±1}`; here `N ≰ ⁅S, N⁆ = 1`, so the hypothesis is genuinely needed (and the conclusion
fails for `φ = id`).

## Route

`Subgroup.map_mono`, `Subgroup.map_commutator`, `Subgroup.commutator_mono`,
`Subgroup.commutator_center_right`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill

/-- **Central images of self-commutator subgroups vanish.**  If `N ≤ ⁅S, N⁆` and `φ` maps `N`
into the centre of `T`, then `φ(N) = ⊥`. -/
theorem map_eq_bot_of_le_commutator_of_map_le_center {S T : Type*} [Group S] [Group T]
    (φ : S →* T) {N : Subgroup S} (hN : N ≤ ⁅(⊤ : Subgroup S), N⁆)
    (hC : N.map φ ≤ Subgroup.center T) : N.map φ = ⊥ := by
  apply le_bot_iff.mp
  have h1 : N.map φ ≤ (⁅(⊤ : Subgroup S), N⁆).map φ := Subgroup.map_mono hN
  have h2 : (⁅(⊤ : Subgroup S), N⁆).map φ ≤ ⁅(⊤ : Subgroup T), Subgroup.center T⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top hC
  have h3 : ⁅(⊤ : Subgroup T), Subgroup.center T⁆ = ⊥ :=
    Subgroup.commutator_center_right (⊤ : Subgroup T)
  rw [← h3]
  exact h1.trans h2

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.map_eq_bot_of_le_commutator_of_map_le_center

/-- Kernel form: under the same hypotheses, `N ≤ ker φ`. -/
theorem le_ker_of_le_commutator_of_map_le_center {S T : Type*} [Group S] [Group T]
    (φ : S →* T) {N : Subgroup S} (hN : N ≤ ⁅(⊤ : Subgroup S), N⁆)
    (hC : N.map φ ≤ Subgroup.center T) : N ≤ φ.ker :=
  (Subgroup.map_eq_bot_iff N).mp (map_eq_bot_of_le_commutator_of_map_le_center φ hN hC)

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.le_ker_of_le_commutator_of_map_le_center

end GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill
