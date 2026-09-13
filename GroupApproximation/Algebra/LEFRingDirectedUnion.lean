import GroupApproximation.Pestov91.LEF
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Increasing unions of LEF rings

`non_mf_groups_exist.tex`, line 1437 (proof of `lem:chain-core-models`, general `X`):
"Coefficient pullback gives injective unital maps of crossed products, and every locally
constant function is constant on a sufficiently fine partition.  Thus $R_{Y_*}$ is an
increasing union of LEF rings and is LEF."

This file supplies the ring-theoretic half of the second sentence.

* `IsLEFRing.of_injective`: LEF passes along injective ring homomorphisms.
* `isLEFRing_of_forall_finset_subset_range`: if every finite subset lies in the range of an
  injective ring homomorphism from an LEF ring, the ring is LEF.
* `isLEFRing_of_monotone_ringHom_range`: an increasing union of images of LEF rings under
  injective ring homomorphisms is LEF.
* `isLEFRing_of_monotone_subrings`: an increasing union of LEF subrings is LEF.
-/

namespace GroupApproximation
namespace Pestov91

universe u v

/-- LEF passes to a ring embedded in an LEF ring by an injective ring homomorphism. -/
theorem IsLEFRing.of_injective {A : Type u} {B : Type v} [Ring A] [Ring B]
    (hB : IsLEFRing B) (φ : A →+* B) (hφ : Function.Injective φ) : IsLEFRing A := by
  classical
  intro t
  obtain ⟨F, _, _, ψ, hinj, h0, h1, hops⟩ := hB (t.image φ)
  have hmem : ∀ a ∈ t, φ a ∈ t.image φ := fun a ha ↦ Finset.mem_image_of_mem φ ha
  refine ⟨F, inferInstance, inferInstance, fun a ↦ ψ (φ a), ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hφ (hinj (Finset.mem_coe.2 (hmem a (Finset.mem_coe.1 ha)))
      (Finset.mem_coe.2 (hmem b (Finset.mem_coe.1 hb))) hab)
  · simp only [map_zero, h0]
  · simp only [map_one, h1]
  · intro a ha b hb
    simpa only [map_add, map_mul] using hops _ (hmem a ha) _ (hmem b hb)

/-- A ring is LEF if each finite subset lies in the range of an injective ring homomorphism
from an LEF ring. -/
theorem isLEFRing_of_forall_finset_subset_range {A : Type u} [Ring A]
    (h : ∀ t : Finset A, ∃ (B : Type v) (_ : Ring B) (φ : B →+* A),
      Function.Injective φ ∧ IsLEFRing B ∧ (t : Set A) ⊆ Set.range φ) :
    IsLEFRing A := by
  classical
  intro t
  obtain ⟨B, _, φ, hφ, hB, hsub⟩ := h t
  obtain ⟨o, hφo, hoφ⟩ : ∃ o : A → B, (∀ a ∈ t, φ (o a) = a) ∧ ∀ b, o (φ b) = b :=
    ⟨Function.invFun φ,
      fun a ha ↦ Function.invFun_eq (Set.mem_range.1 (hsub (Finset.mem_coe.2 ha))),
      Function.leftInverse_invFun hφ⟩
  obtain ⟨F, _, _, ψ, hinj, h0, h1, hops⟩ := hB (t.image o)
  have hmem : ∀ a ∈ t, o a ∈ t.image o := fun a ha ↦ Finset.mem_image_of_mem o ha
  refine ⟨F, inferInstance, inferInstance, fun a ↦ ψ (o a), ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ t := Finset.mem_coe.1 ha
    have hb' : b ∈ t := Finset.mem_coe.1 hb
    have hab' : o a = o b :=
      hinj (Finset.mem_coe.2 (hmem a ha')) (Finset.mem_coe.2 (hmem b hb')) hab
    rw [← hφo a ha', ← hφo b hb', hab']
  · have ho0 : o 0 = 0 := by simpa only [map_zero] using hoφ 0
    simp only [ho0, h0]
  · have ho1 : o 1 = 1 := by simpa only [map_one] using hoφ 1
    simp only [ho1, h1]
  · intro a ha b hb
    have hadd : o (a + b) = o a + o b := by
      rw [← hoφ (o a + o b), map_add, hφo a ha, hφo b hb]
    have hmul : o (a * b) = o a * o b := by
      rw [← hoφ (o a * o b), map_mul, hφo a ha, hφo b hb]
    simpa only [hadd, hmul] using hops _ (hmem a ha) _ (hmem b hb)

/-- An increasing union of images of LEF rings under injective ring homomorphisms is LEF. -/
theorem isLEFRing_of_monotone_ringHom_range {A : Type u} [Ring A] (B : ℕ → Type v)
    [∀ m, Ring (B m)] (φ : ∀ m, B m →+* A) (hφ : ∀ m, Function.Injective (φ m))
    (hmono : Monotone fun m ↦ (φ m).range) (hcover : ∀ a, ∃ m, a ∈ (φ m).range)
    (hLEF : ∀ m, IsLEFRing (B m)) : IsLEFRing A := by
  classical
  refine isLEFRing_of_forall_finset_subset_range fun t ↦ ?_
  obtain ⟨m, hm⟩ : ∃ m, ∀ a ∈ t, a ∈ (φ m).range := by
    choose f hf using hcover
    exact ⟨t.sup f, fun a ha ↦ hmono (Finset.le_sup ha) (hf a)⟩
  exact ⟨B m, inferInstance, φ m, hφ m, hLEF m,
    fun a ha ↦ Set.mem_range.2 (RingHom.mem_range.1 (hm a (Finset.mem_coe.1 ha)))⟩

/-- **An increasing union of LEF rings is LEF**: the ring-theoretic content of
"Thus $R_{Y_*}$ is an increasing union of LEF rings and is LEF"
(`non_mf_groups_exist.tex`, line 1437, proof of `lem:chain-core-models`). -/
theorem isLEFRing_of_monotone_subrings {A : Type u} [Ring A] (B : ℕ → Subring A)
    (hB : Monotone B) (hcover : ∀ a, ∃ m, a ∈ B m) (hLEF : ∀ m, IsLEFRing (B m)) :
    IsLEFRing A := by
  classical
  refine isLEFRing_of_forall_finset_subset_range fun t ↦ ?_
  obtain ⟨m, hm⟩ : ∃ m, ∀ a ∈ t, a ∈ B m := by
    choose f hf using hcover
    exact ⟨t.sup f, fun a ha ↦ hB (Finset.le_sup ha) (hf a)⟩
  exact ⟨B m, inferInstance, (B m).subtype, Subtype.val_injective, hLEF m,
    fun a ha ↦ ⟨⟨a, hm a (Finset.mem_coe.1 ha)⟩, rfl⟩⟩

end Pestov91
end GroupApproximation

#audit_axioms GroupApproximation.Pestov91.IsLEFRing.of_injective
#audit_axioms GroupApproximation.Pestov91.isLEFRing_of_forall_finset_subset_range
#audit_axioms GroupApproximation.Pestov91.isLEFRing_of_monotone_ringHom_range
#audit_axioms GroupApproximation.Pestov91.isLEFRing_of_monotone_subrings
