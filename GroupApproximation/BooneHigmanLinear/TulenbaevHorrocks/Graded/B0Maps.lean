import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.DegOne
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Local
import GroupApproximation.Meta.AxiomGuard

/-!
# `B₀ = A + 𝔄 X A[X]` as a ring of polynomials (lane pal-q111, H.L2/H.L5)

`Graded.horrB0 𝔄` sits inside `A[T, T⁻¹]`.  Its elements have no negative powers of `T`, so they are
polynomials in `X = T`.  This file makes that a ring map.

* `toPolyB0 : B₀ →+* A[X]`, with `toLaurentPos A (toPolyB0 f) = f` (`toLaurentPos_toPolyB0`) and
  `toPolyB0 (c Xⁿ) = c Xⁿ` (`toPolyB0_single`).
* `ev0B0 : B₀ →+* A`, the constant coefficient.
* `resPoly_comp_toPolyB0`: over a local ring with `𝔄 = 𝔪`, reducing an element of `B₀` modulo `𝔪`
  gives the constant `ev0B0 f` mod `𝔪`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace Graded

open Polynomial

variable {A : Type} [CommRing A] {𝔄 : Ideal A}

theorem toLaurentPos_injective : Function.Injective (toLaurentPos A) := by
  rw [toLaurentPos_eq]
  exact Polynomial.toLaurent_injective

theorem toLaurentPos_monomial (n : ℕ) (c : A) :
    toLaurentPos A (Polynomial.monomial n c) = AddMonoidAlgebra.single (n : ℤ) c := by
  rw [toLaurentPos_eq, Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]

variable (𝔄) in
/-- The polynomials whose image in `A[T, T⁻¹]` lies in `B₀`. -/
def polyB0 : Subring A[X] :=
  (horrB0 𝔄).comap (toLaurentPos A)

theorem exists_poly_of_mem_horrB0 {f : LaurentPolynomial A} (hf : f ∈ horrB0 𝔄) :
    ∃ p : A[X], toLaurentPos A p = f := by
  induction f, hf using horrB0_induction with
  | zero => exact ⟨0, map_zero _⟩
  | monomial n c _ => exact ⟨Polynomial.monomial n c, toLaurentPos_monomial n c⟩
  | add f g _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, by rw [map_add, hp, hq]⟩

variable (𝔄) in
/-- `B₀ ≅ polyB0 𝔄`. -/
noncomputable def polyB0Equiv : polyB0 𝔄 ≃+* horrB0 𝔄 :=
  RingEquiv.ofBijective (((toLaurentPos A).comp (polyB0 𝔄).subtype).codRestrict (horrB0 𝔄)
    fun p => p.2) ⟨fun p q hpq => Subtype.ext (toLaurentPos_injective (congrArg Subtype.val hpq)),
    fun f => by
      obtain ⟨p, hp⟩ := exists_poly_of_mem_horrB0 f.2
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      change toLaurentPos A p ∈ horrB0 𝔄
      rw [hp]
      exact f.2⟩

variable (𝔄) in
/-- **An element of `B₀` as a polynomial.** -/
noncomputable def toPolyB0 : horrB0 𝔄 →+* A[X] :=
  (polyB0 𝔄).subtype.comp (polyB0Equiv 𝔄).symm.toRingHom

theorem toLaurentPos_toPolyB0 (f : horrB0 𝔄) :
    toLaurentPos A (toPolyB0 𝔄 f) = (f : LaurentPolynomial A) :=
  congrArg Subtype.val ((polyB0Equiv 𝔄).apply_symm_apply f)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.toLaurentPos_toPolyB0

theorem toLaurentPos_comp_toPolyB0 :
    (toLaurentPos A).comp (toPolyB0 𝔄) = (horrB0 𝔄).subtype :=
  RingHom.ext toLaurentPos_toPolyB0

theorem toPolyB0_single {n : ℕ} {c : A} (hc : n = 0 ∨ c ∈ 𝔄) :
    toPolyB0 𝔄 ⟨AddMonoidAlgebra.single (n : ℤ) c, single_mem_horrB0 hc⟩ =
      Polynomial.monomial n c := by
  apply toLaurentPos_injective
  rw [toLaurentPos_toPolyB0, toLaurentPos_monomial]

variable (𝔄) in
/-- The constant coefficient `B₀ → A`. -/
noncomputable def ev0B0 : horrB0 𝔄 →+* A :=
  (Polynomial.evalRingHom 0).comp (toPolyB0 𝔄)

/-- Two additive maps out of `B₀` that agree on monomials agree. -/
theorem addHom_ext_horrB0 {S : Type*} [AddCommGroup S] {φ ψ : horrB0 𝔄 →+ S}
    (h : ∀ (n : ℕ) (c : A) (hc : n = 0 ∨ c ∈ 𝔄),
      φ ⟨AddMonoidAlgebra.single (n : ℤ) c, single_mem_horrB0 hc⟩ =
        ψ ⟨AddMonoidAlgebra.single (n : ℤ) c, single_mem_horrB0 hc⟩) :
    φ = ψ := by
  ext ⟨f, hf⟩
  induction f, hf using horrB0_induction with
  | zero =>
    have h0 : (⟨0, (horrB0 𝔄).zero_mem⟩ : horrB0 𝔄) = 0 := rfl
    rw [h0, map_zero, map_zero]
  | monomial n c hc => exact h n c hc
  | add f g hf hg ihf ihg =>
    have e : (⟨f + g, (horrB0 𝔄).add_mem hf hg⟩ : horrB0 𝔄) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
    rw [e, map_add, map_add, ihf, ihg]

/-- **Modulo `𝔪`, an element of `B₀` is its constant term.** -/
theorem resPoly_comp_toPolyB0 [IsLocalRing A] :
    (resPoly A).comp (toPolyB0 (IsLocalRing.maximalIdeal A)) =
      (Polynomial.C : IsLocalRing.ResidueField A →+* (IsLocalRing.ResidueField A)[X]).comp
        ((IsLocalRing.residue A).comp (ev0B0 (IsLocalRing.maximalIdeal A))) := by
  have h := addHom_ext_horrB0 (𝔄 := IsLocalRing.maximalIdeal A)
    (φ := ((resPoly A).comp (toPolyB0 (IsLocalRing.maximalIdeal A))).toAddMonoidHom)
    (ψ := ((Polynomial.C : IsLocalRing.ResidueField A →+* (IsLocalRing.ResidueField A)[X]).comp
        ((IsLocalRing.residue A).comp (ev0B0 (IsLocalRing.maximalIdeal A)))).toAddMonoidHom)
    (fun n c hc => by
      change resPoly A (toPolyB0 _ _) =
        Polynomial.C (IsLocalRing.residue A ((Polynomial.evalRingHom 0) (toPolyB0 _ _)))
      rw [toPolyB0_single hc]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [Polynomial.monomial_zero_left, Polynomial.coe_evalRingHom, Polynomial.eval_C]
        exact Polynomial.map_C _
      · have hcm : c ∈ IsLocalRing.maximalIdeal A := hc.resolve_left hn.ne'
        rw [Polynomial.coe_evalRingHom, Polynomial.eval_monomial, zero_pow hn.ne', mul_zero]
        simp only [map_zero]
        change Polynomial.map (IsLocalRing.residue A) (Polynomial.monomial n c) = 0
        rw [Polynomial.map_monomial, (IsLocalRing.residue_eq_zero_iff c).mpr hcm,
          Polynomial.monomial_zero_right])
  exact RingHom.ext fun f => DFunLike.congr_fun h f

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.resPoly_comp_toPolyB0

end Graded
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
