import GroupApproximation.KunThom.CentralizerNormalizationPrunedCore
import GroupApproximation.Matching.ComponentCompletedMultiplicativity

/-!
# Multiplicativity of the pruned core labels

Completing the component labels again on the pruned core can break the product
law only at an ambient product failure, or where one of three images leaves the
core.  Each leaving set injects into the complement of the core, so the core
labels inherit the multiplication error of the component up to three times the
removed mass, which `prunedCore_removed_le` bounds.

* `RetainedComponentExpansion.card_completion_mul_disagreement_le`: the finite
  statement for any three completions on a finite set.
* `ExpanderDecomposition.card_prunedCoreAct_mul_disagreement_le`: the pruned
  core labels.
-/

namespace GroupApproximation
namespace RetainedComponentExpansion

/-- Completions of three permutations on a finite set `D` satisfy the product law
outside the ambient failures `E` and three sets that inject into `univ \ D`. -/
theorem card_completion_mul_disagreement_le {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : Finset Y) (σ τ ρ : Equiv.Perm Y) (p q r : Equiv.Perm D)
    (hp : ∀ x : D, σ (x : Y) ∈ D → (p x : Y) = σ x)
    (hq : ∀ x : D, τ (x : Y) ∈ D → (q x : Y) = τ x)
    (hr : ∀ x : D, ρ (x : Y) ∈ D → (r x : Y) = ρ x)
    (E : Finset Y) (hE : ∀ x : Y, σ x ≠ (τ * ρ) x → x ∈ E) :
    (hammingDisagreement p (q * r)).card ≤ E.card + 3 * (Finset.univ \ D).card := by
  classical
  let bad : Finset D := Finset.univ.filter fun x ↦ σ (x : Y) ≠ τ (ρ (x : Y))
  let L1 : Finset D := Finset.univ.filter fun x ↦ ρ (x : Y) ∉ D
  let L2 : Finset D := Finset.univ.filter fun x ↦ τ (ρ (x : Y)) ∉ D
  let L3 : Finset D := Finset.univ.filter fun x ↦ σ (x : Y) ∉ D
  have hsub : hammingDisagreement p (q * r) ⊆ bad ∪ L1 ∪ L2 ∪ L3 := by
    intro x hx
    have hne : p x ≠ (q * r) x := (mem_hammingDisagreement p (q * r) x).mp hx
    by_cases h1 : ρ (x : Y) ∈ D
    · by_cases h2 : τ (ρ (x : Y)) ∈ D
      · by_cases h3 : σ (x : Y) ∈ D
        · have hb : σ (x : Y) ≠ τ (ρ (x : Y)) := by
            intro heq
            apply hne
            apply Subtype.ext
            have hrx : (r x : Y) = ρ x := hr x h1
            have hmem : τ ((r x : D) : Y) ∈ D := by
              rw [hrx]
              exact h2
            have hqx : (q (r x) : Y) = τ (r x) := hq (r x) hmem
            show (p x : Y) = (q (r x) : Y)
            rw [hqx, hrx, hp x h3, heq]
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)))
  have hbad : bad.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn (fun x : D ↦ (x : Y))
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      exact hE (x : Y) hx'
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  have hL1 : L1.card ≤ (Finset.univ \ D).card := by
    apply Finset.card_le_card_of_injOn (fun x : D ↦ ρ (x : Y))
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'⟩)
    · intro x _ y _ hxy
      exact Subtype.ext (ρ.injective hxy)
  have hL2 : L2.card ≤ (Finset.univ \ D).card := by
    apply Finset.card_le_card_of_injOn (fun x : D ↦ τ (ρ (x : Y)))
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'⟩)
    · intro x _ y _ hxy
      exact Subtype.ext (ρ.injective (τ.injective hxy))
  have hL3 : L3.card ≤ (Finset.univ \ D).card := by
    apply Finset.card_le_card_of_injOn (fun x : D ↦ σ (x : Y))
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'⟩)
    · intro x _ y _ hxy
      exact Subtype.ext (σ.injective hxy)
  have hle := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (bad ∪ L1 ∪ L2) L3
  have hu2 := Finset.card_union_le (bad ∪ L1) L2
  have hu3 := Finset.card_union_le bad L1
  omega

end RetainedComponentExpansion

namespace ExpanderDecomposition

/-- **Multiplicativity on the pruned core.**  The core labels break the product
law at most at the component's multiplication failures plus three times the
removed mass. -/
theorem card_prunedCoreAct_mul_disagreement_le {G : Type} [Group G]
    {S : SoficApproximation G} {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ)
    (C : D.componentIndex n) (g h : G) :
    (hammingDisagreement (D.prunedCoreAct n C (g * h))
      (D.prunedCoreAct n C g * D.prunedCoreAct n C h)).card ≤
      (D.componentMultiplicationError n C g h).card +
        3 * (Finset.univ \ prunedCore D n C).card :=
  RetainedComponentExpansion.card_completion_mul_disagreement_le (prunedCore D n C)
    (D.componentCompletedAction n C (g * h)) (D.componentCompletedAction n C g)
    (D.componentCompletedAction n C h) (D.prunedCoreAct n C (g * h))
    (D.prunedCoreAct n C g) (D.prunedCoreAct n C h)
    (fun x hx ↦ D.prunedCoreAct_agrees n C (g * h) x hx)
    (fun x hx ↦ D.prunedCoreAct_agrees n C g x hx)
    (fun x hx ↦ D.prunedCoreAct_agrees n C h x hx)
    (D.componentMultiplicationError n C g h)
    (fun _ hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

end ExpanderDecomposition
end GroupApproximation
