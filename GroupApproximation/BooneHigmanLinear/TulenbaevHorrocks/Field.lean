import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinTransport
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import GroupApproximation.Meta.AxiomGuard

/-!
# The field case of Horrocks for `St_N` (piece H of the `K₂` program, lane pal-q111)

Tulenbaev (Math. USSR Sb. 45, 1983) uses, in Cor 4.2 and Prop 4.3(a), the Horrocks property of
`St_r` over the residue field `k` of a local ring.  He derives it from Quillen's fundamental theorem
and `K₂` stabilization.  Over a field it follows from `K₂(N, k[X]) = 1` alone:

* `stHorrocksAt_of_K2_eq_bot`: if `K₂(N, k[X]) = 1` and `N > 0`, then `StHorrocksAt k N`.
  - A common image of `α ∈ St_N(k[X])` and `β ∈ St_N(k[X⁻¹])` in `St_N(k[X,X⁻¹])` has a matrix
    with entries in `k[X] ∩ k[X⁻¹] = k` (`polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg`, by
    `LaurentPolynomial.trunc`).
  - That matrix lies in `SL_N(k) = E_N(k)`, so it lifts to `γ ∈ St_N(k)`, and `α = γ = β` because
    `K₂(N, k[X]) = 1`.
* `stHorrocksAt_of_const`: the same from unstable `NK₂` vanishing over `k` (every element of
  `K₂(N, k[X])` is constant), over any field.
* `stHorrocksAt_finiteField_of`: over any finite field, from `FiniteFieldPolyK2Statement`.

The corollaries that need the heavy `K₂` chain (Nagao over `F_p`, `FieldNKStatement`) are in
`TulenbaevHorrocks.FieldCorollaries`, so that this file builds on light imports only.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev

variable {A : Type} [CommRing A]

/-- `X ↦ T` is `Polynomial.toLaurent`. -/
theorem toLaurentPos_eq :
    toLaurentPos A = (Polynomial.toLaurent : A[X] →+* LaurentPolynomial A) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [toLaurentPos, Polynomial.toLaurent_C]
  · simp [toLaurentPos, Polynomial.toLaurent_X]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentPos_eq

/-- `X ↦ T⁻¹` is `Polynomial.toLaurent` followed by `LaurentPolynomial.invert`. -/
theorem toLaurentNeg_eq : toLaurentNeg A =
    (LaurentPolynomial.invert (R := A)).toRingEquiv.toRingHom.comp Polynomial.toLaurent := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [toLaurentNeg, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Polynomial.toLaurent_C]
  · simp [toLaurentNeg, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Polynomial.toLaurent_X]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentNeg_eq

/-- Truncating `q(T⁻¹)` to nonnegative degrees leaves its constant term. -/
theorem trunc_invert_toLaurent (q : A[X]) :
    LaurentPolynomial.trunc (LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      Polynomial.C (q.coeff 0) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, Polynomial.coeff_add, Polynomial.C_add]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T, LaurentPolynomial.trunc_C_mul_T, Polynomial.coeff_monomial]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
      have h2 : n ≠ 0 := by omega
      simp [h1, h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.trunc_invert_toLaurent

/-- **`A[X] ∩ A[X⁻¹] = A` inside `A[X,X⁻¹]`**: if `p(T) = q(T⁻¹)`, then `p` is the constant
`q(0)`. -/
theorem polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg {p q : A[X]}
    (h : toLaurentPos A p = toLaurentNeg A q) : p = Polynomial.C (q.coeff 0) := by
  rw [toLaurentPos_eq, toLaurentNeg_eq] at h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv] at h
  have h' := congrArg LaurentPolynomial.trunc h
  rw [Polynomial.trunc_toLaurent] at h'
  rw [h']
  exact trunc_invert_toLaurent q

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg

/-- The other half: if `p(T) = q(T⁻¹)`, then `q` is the constant `p(0)`. -/
theorem polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg' {p q : A[X]}
    (h : toLaurentPos A p = toLaurentNeg A q) : q = Polynomial.C (p.coeff 0) := by
  apply polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg
  rw [toLaurentPos_eq, toLaurentNeg_eq] at h ⊢
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv] at h ⊢
  rw [h]
  exact (LaurentPolynomial.involutive_invert _).symm

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg'

/-- The matrix of `projection g`. -/
private abbrev projMat {R : Type} [CommRing R] {N : ℕ} (g : SteinbergGroup (Fin N) R) :
    Matrix (Fin N) (Fin N) R :=
  (((projection g : elementaryGroup (Fin N) R) : (Matrix (Fin N) (Fin N) R)ˣ) :
    Matrix (Fin N) (Fin N) R)

private theorem projMat_ringMap {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (g : SteinbergGroup (Fin N) R) : projMat (ringMap f g) = (projMat g).map f := by
  simp only [projMat, projection_ringMap, elementaryGroupMap_apply, elementaryMatrixUnitMap,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply]

theorem toLaurentPos_comp_C : (toLaurentPos A).comp Polynomial.C = LaurentPolynomial.C := by
  ext a
  simp [toLaurentPos]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentPos_comp_C

theorem toLaurentNeg_comp_C : (toLaurentNeg A).comp Polynomial.C = LaurentPolynomial.C := by
  ext a
  simp [toLaurentNeg]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentNeg_comp_C

/-- `St_N(A) → St_N(A[X,X⁻¹])` is injective: evaluation at `T = 1` splits the constants. -/
theorem ringMap_laurentC_injective (N : ℕ) :
    Function.Injective (ringMap (I := Fin N) (LaurentPolynomial.C : A →+* LaurentPolynomial A)) :=
  ringMap_injective_of_leftInverse _ (LaurentPolynomial.eval₂ (RingHom.id A) 1) fun a => by
    rw [LaurentPolynomial.eval₂_C, RingHom.id_apply]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.ringMap_laurentC_injective

/-- **The field case of Horrocks for `St_N`**, from unstable `NK₂` vanishing.  If every element of
`K₂(N, k[X])` is constant (`ElemFP.k2PolyField_ConstStatement k N`, i.e. `K₂(N, k[X]) = C(…)`),
then `St_N(k[X]) → St_N(k[X,X⁻¹]) ← St_N(k[X⁻¹])` are injective and their images meet in
`St_N(k)`.  This is the input of Tulenbaev's Cor 4.2 / Prop 4.3(a) at a residue field. -/
theorem stHorrocksAt_of_const (k : Type) [Field k] {N : ℕ} (hN : 0 < N)
    (hC : ∀ g ∈ K2 (Fin N) k[X], g ∈ (ringMap (I := Fin N) (Polynomial.C : k →+* k[X])).range) :
    StHorrocksAt k N := by
  -- Step 1: every `δ` whose matrix is constant is constant.
  have lift : ∀ (M : Matrix (Fin N) (Fin N) k) (δ : SteinbergGroup (Fin N) k[X]),
      projMat δ = M.map Polynomial.C →
        ∃ γ : SteinbergGroup (Fin N) k, ringMap (Polynomial.C : k →+* k[X]) γ = δ := by
    intro M δ hδ
    have hdetP : (projMat δ).det = 1 :=
      BooneHigman.Metabelian.Absorption.suslin_det_eq_one_of_mem_elementaryGroup
        (projection δ).2
    have hdetM : M.det = 1 := by
      have hC1 : Polynomial.C M.det = Polynomial.C 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hδ, hdetP, Polynomial.C_1]
      exact Polynomial.C_injective hC1
    let u : (Matrix (Fin N) (Fin N) k)ˣ :=
      Matrix.nonsingInvUnit M (by rw [hdetM]; exact isUnit_one)
    have hu : u ∈ elementaryGroup (Fin N) k :=
      BooneHigman.Metabelian.Absorption.specialLinearInElementary_of_field k hN u
        (by change M.det = 1; exact hdetM)
    obtain ⟨γ, hγ⟩ := projection_surjective (I := Fin N) (R := k) ⟨u, hu⟩
    have hγM : projMat γ = M := by
      unfold projMat
      rw [hγ]
      rfl
    have hmem : δ * (ringMap (Polynomial.C : k →+* k[X]) γ)⁻¹ ∈ K2 (Fin N) k[X] := by
      rw [mem_K2_iff, map_mul, map_inv, mul_inv_eq_one]
      apply Subtype.ext
      apply Units.ext
      change projMat δ = projMat (ringMap (Polynomial.C : k →+* k[X]) γ)
      rw [hδ, projMat_ringMap, hγM]
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hC _ hmem)
    refine ⟨w * γ, ?_⟩
    rw [map_mul, hw, inv_mul_cancel_right]
  have key : ∀ α β : SteinbergGroup (Fin N) k[X],
      ringMap (toLaurentPos k) α = ringMap (toLaurentNeg k) β →
        ∃ γ : SteinbergGroup (Fin N) k,
          ringMap (Polynomial.C : k →+* k[X]) γ = α ∧
            ringMap (Polynomial.C : k →+* k[X]) γ = β := by
    intro α β h
    have hentry : ∀ i j, toLaurentPos k (projMat α i j) = toLaurentNeg k (projMat β i j) := by
      intro i j
      have hm := congrArg projMat h
      rw [projMat_ringMap, projMat_ringMap] at hm
      exact congrFun (congrFun hm i) j
    let M : Matrix (Fin N) (Fin N) k := fun i j => (projMat β i j).coeff 0
    have hPM : projMat α = M.map Polynomial.C := by
      ext i j
      exact polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg (hentry i j)
    have hQM : projMat β = M.map Polynomial.C := by
      ext i j
      rw [polynomial_eq_C_of_toLaurentPos_eq_toLaurentNeg' (hentry i j), hPM, Matrix.map_apply,
        Polynomial.coeff_C_zero, Matrix.map_apply]
    obtain ⟨γ₁, hγ₁⟩ := lift M α hPM
    obtain ⟨γ₂, hγ₂⟩ := lift M β hQM
    have h12 : γ₁ = γ₂ := by
      apply ringMap_laurentC_injective N
      rw [← toLaurentPos_comp_C, ← ringMap_ringMap, hγ₁, h, ← hγ₂, ringMap_ringMap,
        toLaurentNeg_comp_C]
    exact ⟨γ₁, hγ₁, h12 ▸ hγ₂⟩
  refine ⟨?_, ?_, key⟩
  · refine (injective_iff_map_eq_one _).mpr fun α hα => ?_
    obtain ⟨γ, hγα, hγ1⟩ := key α 1 (by rw [hα, map_one])
    rw [← hγα, hγ1]
  · refine (injective_iff_map_eq_one _).mpr fun β hβ => ?_
    obtain ⟨γ, hγ1, hγβ⟩ := key 1 β (by rw [hβ, map_one])
    rw [← hγβ, hγ1]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_of_const

/-- **The field case from `K₂(N, k[X]) = 1`**, a special case of `stHorrocksAt_of_const`. -/
theorem stHorrocksAt_of_K2_eq_bot (k : Type) [Field k] {N : ℕ} (hN : 0 < N)
    (hK : K2 (Fin N) k[X] = ⊥) : StHorrocksAt k N := by
  refine stHorrocksAt_of_const k hN fun g hg => ?_
  change g ∈ K2 (Fin N) k[X] at hg
  rw [hK, Subgroup.mem_bot] at hg
  rw [hg]
  exact one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_of_K2_eq_bot

/-- **Horrocks for `St_N` over a finite field**, from `FiniteFieldPolyK2Statement`. -/
theorem stHorrocksAt_finiteField_of {n₀ : ℕ} (h : FiniteFieldPolyK2Statement n₀)
    (k : Type) [Field k] [Finite k] {N : ℕ} (hN : n₀ ≤ N) (h0 : 0 < N) : StHorrocksAt k N :=
  stHorrocksAt_of_K2_eq_bot k h0 (h k N hN)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_finiteField_of

end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
