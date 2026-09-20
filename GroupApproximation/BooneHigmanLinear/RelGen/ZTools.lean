import GroupApproximation.BooneHigmanLinear.RelGen.Split44
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Tools for L–S §4.2: `z`-elements, relative kernels, and constant terms (k2-poly H.L3)

Lane k2-hl3b. Small facts used by L–S Lemma 4.7 and Corollary 4.10 (`RelGen.Lemma47`,
`RelGen.Cor410`), in type A over an index type `I`.

* `zElt_add`: `z_ij(s + t, ξ) = z_ij(s, ξ) · z_ij(t, ξ)`.
* `x_inv_mul_zElt_mul_x`: `z_ij(s, ξ)^{x_ji(η)} = z_ij(s, ξ + η)`, L–S Lemma 4.1(1).
* `ringMap_zElt`, `zElt_mem_relKer`: naturality, and `z_ij(s, ξ) ∈ St̄(R, J)` for `s ∈ J`.
* `relKer_mono`, `relKer_bot`: `J ≤ J'` gives `St̄(R, J) ≤ St̄(R, J')`, and `St̄(R, 0) = 1`.
* Constant terms: `f - C(f(0)) = X · f/X`, so `f - C(f(0)) ∈ X·A[X]`, and `∈ X·M[X]` when
  `f ∈ M[X]`; evaluation at `0` kills `X·A[X]`, hence `St(Φ, X·A[X])` and `St̄(A[X], X·M[X])`.
* Group lemmas: conjugation by `k ∈ H₂` preserves `⁅H₁, H₂⁆`, and then preserves `N ⊔ ⁅H₁, H₂⁆`
  for normal `N`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section Z

variable {I : Type*} [Fintype I] [DecidableEq I] {R S : Type*} [CommRing R] [CommRing S]

/-- `z_ij(s + t, ξ) = z_ij(s, ξ) · z_ij(t, ξ)`. -/
theorem zElt_add (i j : I) (hij : i ≠ j) (s t ξ : R) :
    zElt i j hij (s + t) ξ = zElt i j hij s ξ * zElt i j hij t ξ := by
  simp only [zElt, x_neg, ← x_mul]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zElt_add

/-- L–S Lemma 4.1(1): `x_ji(η)⁻¹ · z_ij(s, ξ) · x_ji(η) = z_ij(s, ξ + η)`. -/
theorem x_inv_mul_zElt_mul_x (i j : I) (hij : i ≠ j) (s ξ η : R) :
    (x j i hij.symm η)⁻¹ * zElt i j hij s ξ * x j i hij.symm η = zElt i j hij s (ξ + η) := by
  simp only [zElt, x_neg, ← x_mul]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_inv_mul_zElt_mul_x

/-- Naturality of `z_ij(s, ξ)`. -/
theorem ringMap_zElt (f : R →+* S) (i j : I) (hij : i ≠ j) (s ξ : R) :
    ringMap f (zElt i j hij s ξ) = zElt i j hij (f s) (f ξ) := by
  simp only [zElt, map_mul, ringMap_x, map_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_zElt

/-- `z_ij(s, ξ) ∈ St̄(R, J)` for `s ∈ J`. -/
theorem zElt_mem_relKer {J : Ideal R} {i j : I} (hij : i ≠ j) {s : R} (hs : s ∈ J) (ξ : R) :
    zElt i j hij s ξ ∈ relKer I J := by
  refine mem_relKer_iff_ringMap.mpr ?_
  rw [ringMap_zElt, Ideal.Quotient.eq_zero_iff_mem.mpr hs]
  simp [zElt]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zElt_mem_relKer

/-- `J ≤ J'` gives `St̄(R, J) ≤ St̄(R, J')`. -/
theorem relKer_mono {J J' : Ideal R} (h : J ≤ J') : relKer I J ≤ relKer I J' := fun g hg => by
  have hid := ringMap_mem_relKer (I := I) (RingHom.id R) (J' := J')
    (by rwa [Ideal.comap_id]) hg
  have e : ringMap (RingHom.id R) g = g :=
    DFunLike.congr_fun GroupApproximation.BooneHigman.SteinbergBasic.ringMap_id g
  rwa [e] at hid

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.relKer_mono

/-- `St̄(R, 0) = 1`: the map `St_I(R) → St_I(R/0)` is injective. -/
theorem relKer_bot : relKer I (⊥ : Ideal R) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  have hinj := GroupApproximation.BooneHigman.SteinbergBasic.ringMap_injective_of_leftInverse
    (I := I) (Ideal.Quotient.mk (⊥ : Ideal R))
    (Ideal.Quotient.lift ⊥ (RingHom.id R) fun a ha => by simpa using ha)
    (fun a => Ideal.Quotient.lift_mk _ _ _)
  exact hinj ((mem_relKer_iff_ringMap.mp hg).trans (map_one _).symm)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.relKer_bot

end Z

section Poly

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A]

/-- `f - C(f(0)) = X · (f / X)`. -/
theorem sub_C_evalZero_eq (f : Polynomial A) :
    f - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f) =
      Polynomial.X * Polynomial.divX f := by
  rw [sub_eq_iff_eq_add, Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero]
  exact (Polynomial.X_mul_divX_add f).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.sub_C_evalZero_eq

/-- `f - C(f(0)) ∈ X·A[X]`. -/
theorem sub_C_evalZero_mem_span_X (f : Polynomial A) :
    f - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f) ∈
      Ideal.span {Polynomial.X} := by
  rw [sub_C_evalZero_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.sub_C_evalZero_mem_span_X

/-- `f - C(f(0)) ∈ X·M[X]` for `f ∈ M[X]`. -/
theorem sub_C_evalZero_mem_xPolyIdeal {M : Ideal A} {f : Polynomial A} (hf : f ∈ polyIdeal M) :
    f - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f) ∈ xPolyIdeal M := by
  have hdiv : Polynomial.divX f ∈ polyIdeal M := by
    rw [polyIdeal, Polynomial.mem_map_C_iff] at hf ⊢
    intro n
    rw [Polynomial.coeff_divX]
    exact hf (n + 1)
  rw [sub_C_evalZero_eq]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hdiv

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.sub_C_evalZero_mem_xPolyIdeal

/-- Evaluation at `0` kills `X·A[X]`. -/
theorem evalZero_eq_zero_of_mem_span_X {s : Polynomial A} (hs : s ∈ Ideal.span {Polynomial.X}) :
    (Polynomial.evalRingHom 0 : Polynomial A →+* A) s = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  simp

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.evalZero_eq_zero_of_mem_span_X

/-- Evaluation at `0` kills `St(Φ, X·A[X])`. -/
theorem xGroup_span_X_le_ker :
    xGroup I (Ideal.span {(Polynomial.X : Polynomial A)}) ≤
      (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A)).ker := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, j, hij, s, hs, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, ringMap_x, evalZero_eq_zero_of_mem_span_X hs, x_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.xGroup_span_X_le_ker

/-- Evaluation at `0` kills `St̄(A[X], X·M[X])`. -/
theorem relKer_xPolyIdeal_le_ker (M : Ideal A) :
    relKer I (xPolyIdeal M) ≤ (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A)).ker := by
  intro g hg
  have h : xPolyIdeal M ≤ (⊥ : Ideal A).comap (Polynomial.evalRingHom 0 : Polynomial A →+* A) :=
    fun s hs => by
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact evalZero_eq_zero_of_mem_span_X (Ideal.mul_le_right hs)
  have hbot := ringMap_mem_relKer (Polynomial.evalRingHom 0 : Polynomial A →+* A) h hg
  rw [relKer_bot, Subgroup.mem_bot] at hbot
  exact MonoidHom.mem_ker.mpr hbot

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.relKer_xPolyIdeal_le_ker

end Poly

section GroupLemmas

variable {G : Type*} [Group G]

/-- Conjugation by `k ∈ H₂` preserves `⁅H₁, H₂⁆`:
`k ⁅g, h⁆ k⁻¹ = ⁅g, k⁆⁻¹ ⁅g, k h⁆`. -/
theorem conj_mem_commutator_of_mem_right {H₁ H₂ : Subgroup G} {k : G} (hk : k ∈ H₂) {c : G}
    (hc : c ∈ ⁅H₁, H₂⁆) : k * c * k⁻¹ ∈ ⁅H₁, H₂⁆ := by
  have hle : ⁅H₁, H₂⁆ ≤ ⁅H₁, H₂⁆.comap (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : k * ⁅g, h⁆ * k⁻¹ = ⁅g, k⁆⁻¹ * ⁅g, k * h⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hg hk))
      (Subgroup.commutator_mem_commutator hg (H₂.mul_mem hk hh))
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hle hc

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_mem_commutator_of_mem_right

/-- If `N` is normal and conjugation by `k` preserves `C`, it preserves `N ⊔ C`. -/
theorem conj_mem_sup_of_normal {N C : Subgroup G} (hN : N.Normal) {k : G}
    (hC : ∀ c ∈ C, k * c * k⁻¹ ∈ C) {y : G} (hy : y ∈ N ⊔ C) : k * y * k⁻¹ ∈ N ⊔ C := by
  have hle : N ⊔ C ≤ (N ⊔ C).comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (fun n hn => ?_) (fun c hc => ?_)
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (le_sup_left : N ≤ N ⊔ C) (hN.conj_mem n hn k)
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (le_sup_right : C ≤ N ⊔ C) (hC c hc)
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hle hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_mem_sup_of_normal

end GroupLemmas

end GroupApproximation.BooneHigmanLinear.RelGen
