import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnital
import Mathlib.Algebra.Exact.Basic

/-!
# The unitized extension of a C⋆-extension

Lane `TWWSch3d3-1D`, work order `WO-3d3-1D` (six-term exactness at `K_*(J)`).
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378).

Let `0 → J →ι A →π B → 0` be an extension of non-unital C⋆-algebras. The index and exponential
maps of M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*,
Definition 9.1.3 and Proposition 12.1.2, are built for an extension with a unital middle term.
For the non-unital extension one uses the unitized extension (RLL §8.3 and §9.1)

  `0 → J → A⁺ → B⁺ → 0`,  `j ↦ ι j`,  `π⁺ = Unitization.starMap π`.

This file provides that extension and the reduction of exactness at `K_*(J)`:

* `unitIncl ι : J →⋆ₙₐ[ℂ] A⁺` is the inclusion `j ↦ ι j`;
* `unitIncl_injective`, `unitIncl_exact`: the unitized sequence is again an extension;
* `starLift_unitIncl`: the unital lift of `unitIncl ι` is `Unitization.starMap ι`;
* `KZeroN.incl_comp_map`: the non-unital `K₀(ι)` followed by `K₀(A) ⊆ K₀(A⁺)` is the
  unital-picture map `K₀(J⁺) → K₀(A⁺)` restricted to `K₀(J)`;
* `exact_comp_injective_iff`, `KZeroN.exact_map_iff`: exactness at `K₀(J)` may be tested after
  the injection `K₀(A) ⊆ K₀(A⁺)`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

section Ext

variable {J A B : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B]

/-- The inclusion `J → A⁺`, `j ↦ ι j`, of the unitized extension (RLL §9.1). -/
def unitIncl (ι : J →⋆ₙₐ[ℂ] A) : J →⋆ₙₐ[ℂ] Unitization ℂ A :=
  (Unitization.inrNonUnitalStarAlgHom ℂ A).comp ι

theorem unitIncl_apply (ι : J →⋆ₙₐ[ℂ] A) (j : J) : unitIncl ι j = (ι j : Unitization ℂ A) :=
  rfl

theorem unitIncl_injective {ι : J →⋆ₙₐ[ℂ] A} (hι : Function.Injective ι) :
    Function.Injective (unitIncl ι) :=
  fun x y h => hι (Unitization.inr_injective (show (ι x : Unitization ℂ A) = ι y from h))

/-- The unital lift `J⁺ → A⁺` of `unitIncl ι` is the unitization of `ι`. -/
theorem starLift_unitIncl (ι : J →⋆ₙₐ[ℂ] A) :
    Unitization.starLift (unitIncl ι) = Unitization.starMap ι :=
  rfl

/-- The scalar part of `π⁺ x` is the scalar part of `x`. -/
theorem fst_starMap (π : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (Unitization.starMap π x).fst = x.fst := by
  show ((Unitization.inl x.fst : Unitization ℂ B) + (π x.snd : Unitization ℂ B)).fst = x.fst
  rw [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]

/-- The non-unital part of `π⁺ x` is `π` of the non-unital part of `x`. -/
theorem snd_starMap (π : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (Unitization.starMap π x).snd = π x.snd := by
  show ((Unitization.inl x.fst : Unitization ℂ B) + (π x.snd : Unitization ℂ B)).snd = π x.snd
  rw [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

/-- **The unitized sequence `J → A⁺ → B⁺` is exact in the middle** (RLL §9.1). -/
theorem unitIncl_exact {ι : J →⋆ₙₐ[ℂ] A} {π : A →⋆ₙₐ[ℂ] B}
    (hex : ∀ a, π a = 0 ↔ a ∈ Set.range ι) (x : Unitization ℂ A) :
    Unitization.starMap π x = 0 ↔ ∃ j, unitIncl ι j = x := by
  constructor
  · intro hx
    have hfst := fst_starMap π x
    have hsnd := snd_starMap π x
    rw [hx, Unitization.fst_zero] at hfst
    rw [hx, Unitization.snd_zero] at hsnd
    obtain ⟨j, hj⟩ := (hex x.snd).mp hsnd.symm
    refine ⟨j, Unitization.ext ?_ ?_⟩
    · rw [unitIncl_apply, Unitization.fst_inr]
      exact hfst
    · rw [unitIncl_apply, Unitization.snd_inr]
      exact hj
  · rintro ⟨j, rfl⟩
    rw [unitIncl_apply, Unitization.starMap_inr, (hex (ι j)).mpr ⟨j, rfl⟩, Unitization.inr_zero]

end Ext

section Exact

/-- Exactness may be tested after composing with an injective homomorphism. -/
theorem exact_comp_injective_iff {M N P Q : Type*} [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup Q] (f : M → N) (g : N →+ P) {h : P →+ Q} (hh : Function.Injective h) :
    Function.Exact f (h.comp g) ↔ Function.Exact f g := by
  show (∀ y, h (g y) = 0 ↔ y ∈ Set.range f) ↔ ∀ y, g y = 0 ↔ y ∈ Set.range f
  exact forall_congr' fun y => by rw [map_eq_zero_iff h hh]

variable {J A : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra A]

/-- `K₀(ι)` followed by `K₀(A) ⊆ K₀(A⁺)` is the map `K₀(J⁺) → K₀(A⁺)` of the unital lift of
`unitIncl ι`, restricted to `K₀(J) ⊆ K₀(J⁺)`. -/
theorem KZeroN.incl_comp_map (ι : J →⋆ₙₐ[ℂ] A) :
    KZeroN.incl.comp (KZeroN.map ι) =
      (KTheory.KZero.map (starRingHomOf (Unitization.starLift (unitIncl ι)))).comp
        KZeroN.incl :=
  AddMonoidHom.ext fun _ => rfl

/-- **Exactness at `K₀(J)` in the unital picture.** A sequence `M → K₀(J) → K₀(A)` is exact iff
it is exact after the injection `K₀(A) ⊆ K₀(A⁺)`, that is, with `K₀(J) → K₀(A)` replaced by
the unital-picture map of the unitized extension. -/
theorem KZeroN.exact_map_iff {M : Type*} (f : M → KZeroN J) (ι : J →⋆ₙₐ[ℂ] A) :
    Function.Exact f ((KTheory.KZero.map (starRingHomOf (Unitization.starLift (unitIncl ι)))).comp
        KZeroN.incl) ↔ Function.Exact f (KZeroN.map ι) := by
  rw [← KZeroN.incl_comp_map]
  exact exact_comp_injective_iff f (KZeroN.map ι) KZeroN.incl_injective

end Exact

end

end TWWSchafhauser
end Full
end GroupApproximation
