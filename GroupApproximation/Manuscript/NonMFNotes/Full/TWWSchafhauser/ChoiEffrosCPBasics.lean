import GroupApproximation.Analysis.CStarStateGNS
import GroupApproximation.Analysis.CStarCPConjugation
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift

/-!
# Choi–Effros lifting, basic facts about completely positive maps

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).  This file
collects the order-free facts about completely positive maps that the lifting
argument uses:

* `stateGNSStarAlgHom` — the GNS representation of a state, bundled as a
  `⋆`-homomorphism into `B(H)`;
* `norm_apply_le_norm_map_one` — a completely positive map between unital
  C⋆-algebras satisfies `‖L a‖ ≤ ‖L 1‖ ‖a‖` (Russo–Dye for cp maps;
  Paulsen, *Completely bounded maps and operator algebras*, Prop. 3.6 and
  Cor. 2.9).  The `B(H)`-valued case is
  `BlackadarKirchberg.CStarExactness.IsCompletelyPositive.norm_apply_le_map_one`;
  the general case follows through the jointly isometric family of GNS
  representations of states (`CStarState.exists_state_norm_le_gnsRep`);
* `compressLinearMap` — the compression `a ↦ c⋆ L(a) c` of a linear map,
  completely positive when `L` is;
* `exists_map_star_mul_self_eq` — the first amplification of a cp map sends
  `x⋆x` to some `p⋆p`.

Sources: M.-D. Choi, E. G. Effros, *The completely positive lifting problem for
C⋆-algebras*, Ann. of Math. (2) **104** (1976), 585–609; N. P. Brown,
N. Ozawa, *C⋆-algebras and finite-dimensional approximations*, Appendix C.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

universe u v

/-! ## The GNS representation of a state as a `⋆`-homomorphism -/

section GNS

variable {B : Type v} [CStarAlgebra B] [Nontrivial B]

/-- The GNS representation of a state, bundled as a `⋆`-algebra homomorphism
into the bounded operators on its (complete) GNS space.  The adjoint relation
`CStarState.State.gnsRep.isAdjoint_star` is exactly `map_star` once the target
is recognised as the C⋆-algebra `B(H)`. -/
def stateGNSStarAlgHom (ω : CStarState.State B) :
    B →⋆ₐ[ℂ] (ω.GNSSpace →L[ℂ] ω.GNSSpace) :=
  { (ω.gnsRep).hom with
    map_star' := fun b ↦ by
      show (ω.gnsRep).hom (star b) = star ((ω.gnsRep).hom b)
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      have h := (ω.gnsRep).isAdjoint_star (star b) x y
      rw [star_star] at h
      exact h }

theorem stateGNSStarAlgHom_apply (ω : CStarState.State B) (b : B) :
    stateGNSStarAlgHom ω b = (ω.gnsRep).hom b := rfl

end GNS

/-! ## The norm of a completely positive map is attained at the unit -/

/-- **Completely positive maps attain their norm at the unit**:
`‖L a‖ ≤ ‖L 1‖ ‖a‖` for a completely positive map between unital C⋆-algebras.
The target is embedded into `B(H)` one state at a time; the GNS family is
jointly isometric, and the `B(H)`-valued estimate is already available. -/
theorem norm_apply_le_norm_map_one {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B] {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) (a : A) :
    ‖L a‖ ≤ ‖L 1‖ * ‖a‖ := by
  obtain (_ | _) := subsingleton_or_nontrivial B
  · rw [Subsingleton.elim (L a) 0, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · obtain ⟨ω, hω⟩ := CStarState.exists_state_norm_le_gnsRep (L a)
    have hρ := CStarExactness.isCompletelyPositive_of_starAlgHom
      (stateGNSStarAlgHom ω).toNonUnitalStarAlgHom
    have hbound : ‖(ω.gnsRep).hom (L a)‖ ≤ ‖(ω.gnsRep).hom (L 1)‖ * ‖a‖ :=
      BlackadarKirchberg.CStarExactness.IsCompletelyPositive.norm_apply_le_map_one
        (hρ.comp hL) a
    exact hω.trans (hbound.trans
      (mul_le_mul_of_nonneg_right (ω.norm_gnsRep_apply_le (L 1)) (norm_nonneg a)))

/-- A completely positive map with `‖L 1‖ ≤ 1` is contractive. -/
theorem norm_apply_le_of_norm_map_one_le {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B] {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) (h1 : ‖L 1‖ ≤ 1) (a : A) :
    ‖L a‖ ≤ ‖a‖ :=
  calc ‖L a‖ ≤ ‖L 1‖ * ‖a‖ := norm_apply_le_norm_map_one hL a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg a)
    _ = ‖a‖ := one_mul _

/-! ## Compressions -/

section Compression

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The compression `a ↦ c⋆ L(a) c` of a linear map by an element `c`. -/
def compressLinearMap (c : B) (L : A →ₗ[ℂ] B) : A →ₗ[ℂ] B :=
  CStarExactness.conjugationLinearMap c ∘ₗ L

@[simp] theorem compressLinearMap_apply (c : B) (L : A →ₗ[ℂ] B) (a : A) :
    compressLinearMap c L a = star c * L a * c := rfl

/-- A compression of a completely positive map is completely positive. -/
theorem isCompletelyPositive_compressLinearMap (c : B) {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) :
    CStarExactness.IsCompletelyPositive (compressLinearMap c L) :=
  (CStarExactness.isCompletelyPositive_conjugationLinearMap c).comp hL

/-- **The first amplification of a completely positive map.**  A completely
positive map sends `x⋆x` to an element of the form `p⋆p`. -/
theorem exists_map_star_mul_self_eq {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) (x : A) :
    ∃ p : B, L (star x * x) = star p * p := by
  classical
  set N : CStarMatrix (Fin 1) (Fin 1) A :=
    ((fun _ _ ↦ x : Matrix (Fin 1) (Fin 1) A) :
      CStarMatrix (Fin 1) (Fin 1) A) with hN_def
  have hN00 : N 0 0 = x := by rw [hN_def]
  have hstarN : (star N : CStarMatrix (Fin 1) (Fin 1) A) 0 0
      = star (N 0 0) := Matrix.star_apply _ _ _
  have hM00 : (star N * N) 0 0 = star x * x := by
    calc (star N * N) 0 0
        = ∑ t : Fin 1, (star N) 0 t * N t 0 := Matrix.mul_apply
      _ = (star N) 0 0 * N 0 0 := Fin.sum_univ_one _
      _ = star (N 0 0) * N 0 0 := by rw [hstarN]
      _ = star x * x := by rw [hN00]
  obtain ⟨P, hP⟩ := hL 1 (star N * N) ⟨N, rfl⟩
  have hstarP : (star P : CStarMatrix (Fin 1) (Fin 1) B) 0 0
      = star (P 0 0) := Matrix.star_apply _ _ _
  have hPentry : (star P * P) 0 0 = star (P 0 0) * P 0 0 := by
    calc (star P * P) 0 0
        = ∑ t : Fin 1, (star P) 0 t * P t 0 := Matrix.mul_apply
      _ = (star P) 0 0 * P 0 0 := Fin.sum_univ_one _
      _ = star (P 0 0) * P 0 0 := by rw [hstarP]
  refine ⟨P 0 0, ?_⟩
  calc L (star x * x) = L ((star N * N) 0 0) := by rw [hM00]
    _ = ((star N * N).map ⇑L) 0 0 := rfl
    _ = (star P * P) 0 0 :=
        congrArg (fun T : CStarMatrix (Fin 1) (Fin 1) B ↦ T 0 0) hP
    _ = star (P 0 0) * P 0 0 := hPentry

end Compression

end

end TWWSchafhauser
end Full
end GroupApproximation
