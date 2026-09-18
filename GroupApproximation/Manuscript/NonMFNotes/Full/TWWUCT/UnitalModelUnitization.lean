import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.UnitalModelKernel
import GroupApproximation.Analysis.KKTheoryKasparov
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# The unital commutative model `C̃ = C ⊕ ℂ`

Lane TWWUCT-G (work order WO-TWWUCT-G), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).

If a non-unital algebra `C` is commutative then its minimal unitization `C̃` is a separable
unital commutative C⋆-algebra, and `0 → C → C̃ → ℂ → 0` is split by the unit.  This is the
unital commutative model used to pass from the non-unital `KKn`-commutative class to the unital
UCT class `KasparovTheory.SatisfiesUCT` (Blackadar, *K-Theory for Operator Algebras*, 22.3.5;
for `C = C₀(Y)` one has `C̃ = C(Y⁺)`).

Contents:
* `separableSpace_unitization`: `C̃` is separable when `C` is;
* `unitalModel C : KK.SepCStarAlgebra`, and `unitalModel_isCommutative`;
* `unitizationSplitExtension C : SplitExtension C C̃ ℂ`.
-/

namespace GroupApproximation.Full.TWWUCT.UnitalModel

open Bootstrap

noncomputable section

/-- **The unitization of a separable C⋆-algebra is separable**: `(c, a) ↦ c • 1 + a` is a
continuous surjection `ℂ × C → C̃`.  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
instance separableSpace_unitization {C : Type} [NonUnitalCStarAlgebra C]
    [TopologicalSpace.SeparableSpace C] : TopologicalSpace.SeparableSpace (Unitization ℂ C) := by
  let assemble : ℂ × C → Unitization ℂ C := fun x ↦ Unitization.inl x.1 + (x.2 : Unitization ℂ C)
  have hcontinuous : Continuous assemble := by
    have halg : Continuous (algebraMap ℂ (Unitization ℂ C)) :=
      (LipschitzWith.of_dist_le_mul (K := 1) fun c d ↦ by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
        change ‖algebraMap ℂ (Unitization ℂ C) c - algebraMap ℂ (Unitization ℂ C) d‖ ≤ ‖c - d‖
        rw [← map_sub (algebraMap ℂ (Unitization ℂ C)) c d, norm_algebraMap']).continuous
    have hinl : Continuous (Unitization.inl : ℂ → Unitization ℂ C) := by
      simpa only [Unitization.algebraMap_eq_inl] using halg
    exact (hinl.comp continuous_fst).add (Unitization.continuous_inr.comp continuous_snd)
  have hsurjective : Function.Surjective assemble := fun x ↦
    ⟨(x.fst, x.snd), Unitization.inl_fst_add_inr_snd_eq x⟩
  exact hsurjective.denseRange.separableSpace hcontinuous

/-- **The unital model** `C̃` of a separable non-unital C⋆-algebra `C`: its minimal
unitization, as a separable unital C⋆-algebra.  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def unitalModel (C : SepNUCStarAlgebra) : KK.SepCStarAlgebra.{0} where
  carrier := Unitization ℂ C

/-- The unitization of a commutative algebra is commutative. -/
theorem unitization_mul_comm {C : Type} [NonUnitalCStarAlgebra C]
    (hC : ∀ x y : C, x * y = y * x) (x y : Unitization ℂ C) : x * y = y * x := by
  refine Unitization.ext ?_ ?_
  · calc (x * y).fst = x.fst * y.fst := Unitization.fst_mul x y
      _ = y.fst * x.fst := mul_comm x.fst y.fst
      _ = (y * x).fst := (Unitization.fst_mul y x).symm
  · calc (x * y).snd = x.fst • y.snd + y.fst • x.snd + x.snd * y.snd := Unitization.snd_mul x y
      _ = y.fst • x.snd + x.fst • y.snd + y.snd * x.snd := by
        rw [hC x.snd y.snd, add_comm (x.fst • y.snd)]
      _ = (y * x).snd := (Unitization.snd_mul y x).symm

/-- **The unital model of a commutative algebra is commutative.**  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
theorem unitalModel_isCommutative {C : SepNUCStarAlgebra} (hC : C.IsCommutative) :
    (unitalModel C).IsCommutative :=
  fun x y => unitization_mul_comm (C := C) hC x y

/-- The augmentation character `C̃ → ℂ`, `c • 1 + a ↦ c`. -/
def unitizationFst (C : SepNUCStarAlgebra) : Unitization ℂ C →⋆ₐ[ℂ] ℂ :=
  { Unitization.fstHom ℂ C with
    map_star' := Unitization.fst_star }

theorem unitization_fst_eq_zero_iff {C : SepNUCStarAlgebra} (a : Unitization ℂ C) :
    a.fst = 0 ↔ ∃ c : C, (c : Unitization ℂ C) = a :=
  ⟨fun h => ⟨a.snd, Unitization.ext h.symm rfl⟩, by
    rintro ⟨c, rfl⟩
    exact Unitization.fst_inr ℂ c⟩

/-- **The unitization split extension** `0 → C → C̃ → ℂ → 0`, split by the unit.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def unitizationSplitExtension (C : SepNUCStarAlgebra) :
    SplitExtension C (SepNUCStarAlgebra.of (unitalModel C)) (SepNUCStarAlgebra.of ℂ) where
  incl := Unitization.inrNonUnitalStarAlgHom ℂ C
  quot := (unitizationFst C).toNonUnitalStarAlgHom
  incl_injective := Unitization.inr_injective (R := ℂ) (A := C)
  exact := fun a => unitization_fst_eq_zero_iff (C := C) a
  sec := (StarAlgHom.ofId ℂ (Unitization ℂ C)).toNonUnitalStarAlgHom
  quot_sec := fun b => AlgHomClass.commutes (unitizationFst C) b

end

end GroupApproximation.Full.TWWUCT.UnitalModel
