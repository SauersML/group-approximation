import GroupApproximation.BooneHigmanLinear.LSCore.ZStable
import GroupApproximation.Meta.AxiomGuard

/-!
# Lavrenov–Sinchuk, Remark 5.13 and Lemma 5.15: `P̃_α(0)`, `P̃_α(*)` are stable under `x_β(b)`

Let `A` be local with maximal ideal `M`, `α = (i, j)`, and `|I| ≥ 5`. The inputs from H.L3
(lane bh-pal-wire) enter as hypotheses: Theorem 4.4 (`Thm44Statement`), the split (4.4)
(`Split44Statement`) and Corollary 4.10 (`Cor410Statement`).
* `pStar_le_relKer`, `ev_mem_zAlpha`: `P̃_α(*) ≤ St̄(A[X], M[X])`, and evaluation at `X = 0`
  sends it into `Z_α(A, M)`.
* `mem_pStar_of` (**Remark 5.13**): conversely, `h ∈ St̄(A[X], M[X])` with `h(0) ∈ Z_α(A, M)`
  lies in `P̃_α(*)`. Write `h = h(0) · k` with `k ∈ K(A[X], M[X])` (4.4); then `k ∈ P̃_α(*)` by
  Lemma 5.12, and `h(0) ∈ P̃_α(0)` by Remark 5.11.
* `conj_mem_pStar_of_Z` (**Lemma 5.15** for `P̃_α(*)`): for `β = (a, c) ∈ Z(α)` and `b ∈ A`,
  `x_β(b) g x_β(-b) ∈ P̃_α(*)` for `g ∈ P̃_α(*)`, by stability of `Z_α(A, M)` (`cj_mem_zAlpha`).
* `conj_mem_pZero_of_Z` (**Lemma 5.15** for `P̃_α(0)`): as above, since `p_α` is unchanged
  (`pAlpha_conj_Z`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen
open Polynomial (X C)

variable {I : Type} [Fintype I] [DecidableEq I] {A : Type} [CommRing A] {M : Ideal A}

theorem coeff_zero_mem {f : Polynomial A} (hf : f ∈ polyIdeal M) :
    Polynomial.evalRingHom 0 f ∈ M := by
  rw [Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero]
  exact Ideal.mem_map_C_iff.mp hf 0

theorem mk_eq_zero {J : Ideal (Polynomial A)} {f : Polynomial A} (hf : f ∈ J) :
    Ideal.Quotient.mk J f = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- `P̃_α(*) ≤ St̄(A[X], M[X])`. -/
theorem pStar_le_relKer {i j : I} (hij : i ≠ j) : pStar M i j hij ≤ relKer I (polyIdeal M) := by
  rw [pStar, Subgroup.closure_le]
  intro g hg
  change g ∈ K2Found.relSt I _
  rw [K2Found.mem_relSt]
  rw [Set.mem_union] at hg
  rcases hg with hg | ⟨m, hm, rfl⟩
  · unfold pGens at hg
    rcases hg with (((hg | hg) | hg) | hg) | hg
    · obtain ⟨p, q, hpq, f, ξ, hf, -, rfl⟩ := hg
      rw [ringMap_zElt, mk_eq_zero (Ideal.mul_mem_left _ X hf), zElt_zero_left]
    · obtain ⟨p, q, hpq, f, ξ, hf, -, rfl⟩ := hg
      rw [ringMap_zElt, mk_eq_zero hf, zElt_zero_left]
    · obtain ⟨p, q, hpq, f, ξ, hf, -, rfl⟩ := hg
      rw [ringMap_zElt, mk_eq_zero hf, zElt_zero_left]
    · obtain ⟨f, hf, rfl⟩ := hg
      rw [ringMap_x, mk_eq_zero (Ideal.mul_mem_left _ _ hf), x_zero]
    · obtain ⟨f, hf, rfl⟩ := hg
      rw [ringMap_x, mk_eq_zero hf, x_zero]
  · rw [ringMap_x, mk_eq_zero (Ideal.mul_mem_right X _ (Ideal.mem_map_of_mem _ hm)), x_zero]

#audit_axioms pStar_le_relKer

/-- Evaluation at `X = 0` sends `P̃_α(*)` into `Z_α(A, M)`. -/
theorem ev_mem_zAlpha {i j : I} (hij : i ≠ j) {g : SteinbergGroup I (Polynomial A)}
    (hg : g ∈ pStar M i j hij) :
    ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g ∈ zAlpha M i j := by
  have hX : ∀ f : Polynomial A, Polynomial.evalRingHom 0 (X * f) = 0 := fun f => by simp
  have hX2 : ∀ f : Polynomial A, Polynomial.evalRingHom 0 (X ^ 2 * f) = 0 := fun f => by simp
  have hCX : ∀ m : A, Polynomial.evalRingHom 0 (C m * X) = 0 := fun m => by simp
  have hle : (pStar M i j hij).map (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A)) ≤
      zAlpha M i j := by
    rw [pStar, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_union] at hg
    rcases hg with hg | ⟨m, -, rfl⟩
    · unfold pGens at hg
      rcases hg with (((hg | hg) | hg) | hg) | hg
      · obtain ⟨p, q, hpq, f, ξ, -, -, rfl⟩ := hg
        rw [ringMap_zElt, hX, zElt_zero_left]
        exact one_mem _
      · obtain ⟨p, q, hpq, f, ξ, hf, hA, rfl⟩ := hg
        rw [ringMap_zElt, hX, zElt_zero_right']
        exact Subgroup.subset_closure (Or.inl ⟨p, q, hpq, _, coeff_zero_mem hf, Or.inr hA, rfl⟩)
      · obtain ⟨p, q, hpq, f, ξ, hf, hO, rfl⟩ := hg
        rw [ringMap_zElt]
        exact zA_z hpq hO (coeff_zero_mem hf) _
      · obtain ⟨f, -, rfl⟩ := hg
        rw [ringMap_x, hX2, x_zero]
        exact one_mem _
      · obtain ⟨f, hf, rfl⟩ := hg
        rw [ringMap_x]
        exact Subgroup.subset_closure (Or.inl ⟨i, j, hij, _, coeff_zero_mem hf, Or.inl ⟨rfl, rfl⟩,
          rfl⟩)
    · rw [ringMap_x, hCX, x_zero]
      exact one_mem _
  exact hle ⟨g, hg, rfl⟩

#audit_axioms ev_mem_zAlpha

theorem pAlpha_xC {i j a c : I} (hij : i ≠ j) (hac : a ≠ c) (haj : a ≠ j) (b : A) :
    pAlpha i j (x a c hac (C b)) = 0 := by
  rw [pAlpha, mat_x, Matrix.add_apply, Matrix.single_apply_of_ne (fun h => haj h.1), add_zero,
    Matrix.one_apply_ne hij.symm, Polynomial.coeff_zero]

/-- `p_α` is unchanged by conjugation with `x_β(b)`, `β ∈ Z(α)`, `b ∈ A`. -/
theorem pAlpha_conj_Z {i j : I} (hij : i ≠ j) {a c : I} (hac : a ≠ c) (hZ : InZ i j a c) (b : A)
    {g : SteinbergGroup I (Polynomial A)}
    (hg : RowCol i j ((Polynomial.evalRingHom 0 : Polynomial A →+* A).mapMatrix (mat g))) :
    pAlpha i j (x a c hac (C b) * g * (x a c hac (C b))⁻¹) = pAlpha i j g := by
  have hy : ∀ b' : A, RowCol i j
      ((Polynomial.evalRingHom 0 : Polynomial A →+* A).mapMatrix (mat (x a c hac (C b')))) := by
    intro b'
    rw [← mat_ringMap, ringMap_x]
    exact rowCol_x hac hZ.1 hZ.2 _
  have hy' : RowCol i j ((Polynomial.evalRingHom 0 : Polynomial A →+* A).mapMatrix
      (mat (x a c hac (C b))⁻¹)) := by
    rw [← x_neg, ← map_neg]
    exact hy (-b)
  have hgy : RowCol i j ((Polynomial.evalRingHom 0 : Polynomial A →+* A).mapMatrix
      (mat (g * (x a c hac (C b))⁻¹))) := by
    rw [mat_mul, map_mul]
    exact hg.mul hy'
  rw [mul_assoc, pAlpha_mul_of_rowCol (hy b) hgy, pAlpha_mul_of_rowCol hg hy',
    pAlpha_xC hij hac hZ.1, ← x_neg, ← map_neg, pAlpha_xC hij hac hZ.1, zero_add, add_zero]

#audit_axioms pAlpha_conj_Z

section Local

variable [IsLocalRing A]

/-- **L–S Remark 5.13**: `h ∈ St̄(A[X], 𝔪[X])` with `h(0) ∈ Z_α(A, 𝔪)` lies in `P̃_α(*)`. -/
theorem mem_pStar_of (h44 : Thm44Statement) (hs : Split44Statement) (h410 : Cor410Statement)
    (h3 : ThirdIndex I) {i j : I} (hij : i ≠ j) {h : SteinbergGroup I (Polynomial A)}
    (hh : h ∈ relKer I (polyIdeal (IsLocalRing.maximalIdeal A)))
    (h0 : ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) h ∈
      zAlpha (IsLocalRing.maximalIdeal A) i j) :
    h ∈ pStar (IsLocalRing.maximalIdeal A) i j hij := by
  obtain ⟨-, hk⟩ := hs I A (IsLocalRing.maximalIdeal A) h hh
  have hC : ringMap (C : A →+* Polynomial A)
      (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) h) ∈
      pStar (IsLocalRing.maximalIdeal A) i j hij :=
    pZero_le_pStar _ i j hij (map_zAlpha_le _ i j hij ⟨_, h0, rfl⟩)
  have := mul_mem hC (polyKer_le_pStar h44 h410 h3 hij hk)
  rwa [mul_inv_cancel_left] at this

#audit_axioms mem_pStar_of

/-- **L–S Lemma 5.15** for `P̃_α(*)`: stable under `x_β(b)`, `β ∈ Z(α)`, `b ∈ A`. -/
theorem conj_mem_pStar_of_Z (h44 : Thm44Statement) (hs : Split44Statement)
    (h410 : Cor410Statement) (h3 : ThirdIndex I) (h5 : 5 ≤ Fintype.card I) {i j : I}
    (hij : i ≠ j) {a c : I} (hac : a ≠ c) (hZ : InZ i j a c) (b : A)
    {g : SteinbergGroup I (Polynomial A)} (hg : g ∈ pStar (IsLocalRing.maximalIdeal A) i j hij) :
    x a c hac (C b) * g * (x a c hac (C b))⁻¹ ∈ pStar (IsLocalRing.maximalIdeal A) i j hij := by
  have hN : (relKer I (polyIdeal (IsLocalRing.maximalIdeal A))).Normal := by
    unfold relKer
    infer_instance
  refine mem_pStar_of h44 hs h410 h3 hij (hN.conj_mem _ (pStar_le_relKer hij hg) _) ?_
  have e : ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A)
      (x a c hac (C b) * g * (x a c hac (C b))⁻¹) =
      cj (x a c hac (-b)) (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g) := by
    rw [map_mul, map_mul, map_inv, ringMap_x, cj, x_neg, inv_inv]
    simp
  rw [e]
  exact cj_mem_zAlpha h5 hij hac hZ (-b) (ev_mem_zAlpha hij hg)

#audit_axioms conj_mem_pStar_of_Z

/-- **L–S Lemma 5.15** for `P̃_α(0)`. -/
theorem conj_mem_pZero_of_Z (h44 : Thm44Statement) (hs : Split44Statement)
    (h410 : Cor410Statement) (h3 : ThirdIndex I) (h5 : 5 ≤ Fintype.card I) {i j : I}
    (hij : i ≠ j) {a c : I} (hac : a ≠ c) (hZ : InZ i j a c) (b : A)
    {g : SteinbergGroup I (Polynomial A)} (hg : g ∈ pZero (IsLocalRing.maximalIdeal A) i j hij) :
    x a c hac (C b) * g * (x a c hac (C b))⁻¹ ∈ pZero (IsLocalRing.maximalIdeal A) i j hij := by
  obtain ⟨k, hki, hkj⟩ := h3 i j
  have hg' := pZero_le_pStar _ i j hij hg
  have hs' := conj_mem_pStar_of_Z h44 hs h410 h3 h5 hij hac hZ b hg'
  obtain ⟨m, hm, g₀, hg₀, he⟩ :=
    (mem_pStar_iff hij (fun h => hki h.symm) (fun h => hkj h.symm)).mp hs'
  have hp : pAlpha i j (x a c hac (C b) * g * (x a c hac (C b))⁻¹) = 0 := by
    rw [pAlpha_conj_Z hij hac hZ b (rowCol_ev_of_mem_pStar hg'), pAlpha_eq_zero hg]
  rw [he, pAlpha_decomp hij hm hg₀] at hp
  rw [he, hp, map_zero, zero_mul, x_zero, mul_one]
  exact hg₀

#audit_axioms conj_mem_pZero_of_Z

end Local

end LSCore
end BooneHigmanLinear
end GroupApproximation
