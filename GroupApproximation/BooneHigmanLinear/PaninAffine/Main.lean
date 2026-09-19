import GroupApproximation.BooneHigmanLinear.PaninAffine.Line
import GroupApproximation.BooneHigmanLinear.PaninAffine.Geometry
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The affine presentation over an infinite field (lane k2-panin, board piece GEO)

`infiniteFieldAffineMonicFibre : InfiniteFieldAffineMonicFibreStatement`.

Let `K` be infinite, `M` a maximal ideal of `R = K[s₀..sₙ]` with point `x` over `κ = R/M`, and
`f ∈ M`, `f' ∉ M` relatively prime. A shear `φ` (`s₀ ↦ s₀`, `sⱼ₊₁ ↦ sⱼ₊₁ + aⱼ s₀`) with `a ∈ Kⁿ`
works:
1. **The generic line** `t ↦ x + t(1, A)` in direction `A = (A₁..Aₙ)`. Restricting `f, f'` to it
   gives `P, Q ∈ κ[A][t]` (`genLine`), relatively prime by `isRelPrime_genLine`. This uses
   stability under `K → κ` and translation, and the blow-up chart with `f'(x) ≠ 0`. By Gauss
   they are coprime over `κ(A)`, so their resultant `Res ∈ κ[A]` is nonzero.
2. **Choosing `a`.** Take a `K`-linear `ℓ : κ → K` with `ℓ(Res) ≠ 0` coefficientwise, and use
   that `K` is infinite. Some `a ∈ Kⁿ` has both the leading coefficient `lcPoly f (a)` and
   `ℓ(Res(a))` nonzero. Then `Res(a) ≠ 0`, so the restrictions of `f, f'` to the line through
   `x` in direction `(1, a)` are coprime (`exists_direction`).
3. **Reading off.** After the shear `φ_a`, `φ f` is monic in `s₀` up to `lcPoly f (a)`. The
   fibre of `φ_a f, φ_a f'` over the image of `x` is exactly that line, reparametrized
   (`fibre_eq`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open MvPolynomial

section Transl

variable {κ : Type*} [Field κ] {n : ℕ}

/-- Translation `sᵢ ↦ sᵢ + xᵢ` over `κ`. -/
noncomputable def transl (x : Fin (n + 1) → κ) :
    MvPolynomial (Fin (n + 1)) κ →ₐ[κ] MvPolynomial (Fin (n + 1)) κ :=
  aeval fun i => X i + C (x i)

theorem transl_X (x : Fin (n + 1) → κ) (i : Fin (n + 1)) : transl x (X i) = X i + C (x i) := by
  simp [transl]

theorem transl_C (x : Fin (n + 1) → κ) (c : κ) : transl x (C c) = C c := by
  simp [transl, MvPolynomial.algebraMap_eq]

theorem transl_comp_neg (x : Fin (n + 1) → κ) : (transl x).comp (transl (-x)) = AlgHom.id κ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, transl_X, map_add, transl_C, Pi.neg_apply, C_neg]
  ring

/-- Translation as an automorphism. -/
noncomputable def translEquiv (x : Fin (n + 1) → κ) :
    MvPolynomial (Fin (n + 1)) κ ≃ₐ[κ] MvPolynomial (Fin (n + 1)) κ :=
  AlgEquiv.ofAlgHom (transl x) (transl (-x)) (transl_comp_neg x)
    (by simpa using transl_comp_neg (-x))

theorem constantCoeff_transl (x : Fin (n + 1) → κ) (g : MvPolynomial (Fin (n + 1)) κ) :
    constantCoeff (transl x g) = eval x g := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [transl_C, constantCoeff_C, eval_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, transl_X, map_add, constantCoeff_X, constantCoeff_C, zero_add, eval_X]

end Transl

section LineMap

variable {K κ : Type*} [CommRing K] [CommRing κ] [Algebra K κ] {n : ℕ}

/-- Restriction to the line through `x` in direction `(1, a)`: `sᵢ ↦ xᵢ + vᵢ t`. -/
noncomputable def lineMap (x : Fin (n + 1) → κ) (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] Polynomial κ :=
  aeval fun i => Polynomial.C (x i) +
    Polynomial.C ((Fin.cons (1 : κ) (fun j => algebraMap K κ (a j)) : Fin (n + 1) → κ) i) *
      Polynomial.X

end LineMap

section Direction

variable {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {n : ℕ}

/-- Restriction to the generic line `t ↦ x + t (1, A)`, with coefficients in `κ[A]`. -/
noncomputable def genLine (x : Fin (n + 1) → κ) (g : MvPolynomial (Fin (n + 1)) K) :
    Polynomial (MvPolynomial (Fin n) κ) :=
  chart κ n (transl x (map (algebraMap K κ) g))

theorem map_genLine (x : Fin (n + 1) → κ) (a : Fin n → K) (g : MvPolynomial (Fin (n + 1)) K) :
    (genLine x g).map (MvPolynomial.eval fun j => algebraMap K κ (a j)) = lineMap x a g := by
  induction g using MvPolynomial.induction_on with
  | C r =>
    simp [genLine, lineMap, transl_C, chart_C, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [genLine, map_add, Polynomial.map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [genLine, map_mul, Polynomial.map_mul, MvPolynomial.map_X] at hp ⊢
    rw [hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [transl_X, map_add, chart_X_zero, chart_C, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_C, eval_C, lineMap, aeval_X, Fin.cons_zero, map_one, one_mul]
      ring
    · simp only [transl_X, map_add, chart_X_succ, chart_C, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, eval_C, eval_X, lineMap, aeval_X, Fin.cons_succ]
      ring

theorem isRelPrime_genLine {x : Fin (n + 1) → κ} {f f' : MvPolynomial (Fin (n + 1)) K}
    (h : IsRelPrime f f') (hx : eval x (map (algebraMap K κ) f') ≠ 0) :
    IsRelPrime (genLine x f) (genLine x f') := by
  have h1 : IsRelPrime (map (algebraMap K κ) f) (map (algebraMap K κ) f') :=
    isRelPrime_map_of_isRelPrime h
  have h2 := isRelPrime_map_mulEquiv (translEquiv x).toRingEquiv.toMulEquiv h1
  exact isRelPrime_chart h2 (by
    show constantCoeff (transl x (map (algebraMap K κ) f')) ≠ 0
    rw [constantCoeff_transl]
    exact hx)

theorem exists_eval_ne_zero {σ : Type*} [Infinite K] {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ a : σ → K, eval a P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (MvPolynomial.funext fun a => by rw [h a, map_zero])

/-- **A good direction exists.** -/
theorem exists_direction [Infinite K] {x : Fin (n + 1) → κ} {f f' : MvPolynomial (Fin (n + 1)) K}
    (hrel : IsRelPrime f f') (hf0 : f ≠ 0) (hx : eval x (map (algebraMap K κ) f') ≠ 0) :
    ∃ a : Fin n → K, eval a (lcPoly f) ≠ 0 ∧ IsCoprime (lineMap x a f) (lineMap x a f') := by
  classical
  have hPQ := isRelPrime_genLine hrel hx
  have hQcoeff : (genLine x f').coeff 0 = C (eval x (map (algebraMap K κ) f')) := by
    rw [genLine, chart_coeff_zero, constantCoeff_transl]
  have hQ0 : genLine x f' ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hQcoeff
    exact hx (MvPolynomial.C_eq_zero.mp hQcoeff.symm)
  by_cases hdeg : (genLine x f).natDegree = 0 ∧ (genLine x f').natDegree = 0
  · obtain ⟨a, ha⟩ := exists_eval_ne_zero (lcPoly_ne_zero hf0)
    refine ⟨a, ha, ?_⟩
    rw [← map_genLine, ← map_genLine, Polynomial.eq_C_of_natDegree_eq_zero hdeg.2, hQcoeff,
      Polynomial.map_C, eval_C]
    exact ⟨0, Polynomial.C (eval x (map (algebraMap K κ) f'))⁻¹, by
      rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ hx, Polynomial.C_1]⟩
  · have hH : (genLine x f).natDegree ≠ 0 ∨ (genLine x f').natDegree ≠ 0 := not_and_or.mp hdeg
    have hinj : Function.Injective
        (algebraMap (MvPolynomial (Fin n) κ) (FractionRing (MvPolynomial (Fin n) κ))) :=
      IsFractionRing.injective _ _
    have hcop := isCoprime_map_fractionRing_of_isRelPrime hPQ hQ0
    have key : Polynomial.resultant
          ((genLine x f).map (algebraMap _ (FractionRing (MvPolynomial (Fin n) κ))))
          ((genLine x f').map (algebraMap _ (FractionRing (MvPolynomial (Fin n) κ)))) =
        algebraMap _ (FractionRing (MvPolynomial (Fin n) κ))
          (Polynomial.resultant (genLine x f) (genLine x f')) := by
      rw [← Polynomial.resultant_map_map, Polynomial.natDegree_map_eq_of_injective hinj,
        Polynomial.natDegree_map_eq_of_injective hinj]
    have hRes : Polynomial.resultant (genLine x f) (genLine x f') ≠ 0 := by
      intro h0
      have h1 : Polynomial.resultant
          ((genLine x f).map (algebraMap _ (FractionRing (MvPolynomial (Fin n) κ))))
          ((genLine x f').map (algebraMap _ (FractionRing (MvPolynomial (Fin n) κ)))) = 0 := by
        rw [key, h0, map_zero]
      exact (Polynomial.resultant_eq_zero_iff.mp h1).2 hcop
    obtain ⟨ℓ, hℓ⟩ := exists_coeffMap_ne_zero (K := K) hRes
    obtain ⟨a, ha⟩ := exists_eval_ne_zero (mul_ne_zero (lcPoly_ne_zero hf0) hℓ)
    rw [map_mul] at ha
    obtain ⟨ha1, ha2⟩ := mul_ne_zero_iff.mp ha
    refine ⟨a, ha1, ?_⟩
    have hev : MvPolynomial.eval (fun j => algebraMap K κ (a j))
        (Polynomial.resultant (genLine x f) (genLine x f')) ≠ 0 := by
      intro h0
      apply ha2
      rw [eval_coeffMap, h0, map_zero]
    rw [← map_genLine, ← map_genLine]
    obtain ⟨p, q, -, -, hpq⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      ((genLine x f).map (MvPolynomial.eval fun j => algebraMap K κ (a j)))
      ((genLine x f').map (MvPolynomial.eval fun j => algebraMap K κ (a j)))
      (m := (genLine x f).natDegree) (n := (genLine x f').natDegree)
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hH
    rw [Polynomial.resultant_map_map] at hpq
    exact isCoprime_of_eq_C hpq hev

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_direction

end Direction

section Fibre

/-- The fibre of the sheared polynomials over the image of the point is the line through the point
in direction `(1, a)`, reparametrized by `t ↦ t - x₀`. -/
theorem fibre_eq {K : Type} [Field K] {n : ℕ} (a : Fin n → K)
    (M : Ideal (MvPolynomial (Fin (n + 1)) K)) (x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K ⧸ M)
    (hx : ∀ i, x i = Ideal.Quotient.mk M (X i)) (g : MvPolynomial (Fin (n + 1)) K) :
    (finSuccEquiv K n (shear a g)).map (fibreMap M (shear a)) =
      (lineMap x a g).comp (Polynomial.X - Polynomial.C (x 0)) := by
  have hfib : ∀ j : Fin n,
      fibreMap M (shear a) (X j) = x j.succ - algebraMap K _ (a j) * x 0 := by
    intro j
    show Ideal.Quotient.mk M ((shear a).symm (rename Fin.succ (X j))) = _
    rw [rename_X, shear_symm_apply, shearHom_X_succ, map_add, map_mul, ← hx, ← hx,
      ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, Pi.neg_apply, map_neg]
    ring
  have hfibC : ∀ c : K, fibreMap M (shear a) (C c) = algebraMap K _ c := by
    intro c
    show Ideal.Quotient.mk M ((shear a).symm (rename Fin.succ (C c))) = _
    rw [rename_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Ideal.Quotient.mk_algebraMap]
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [shear_apply, show shearHom a (C c) = C c by simp [shearHom], finSuccEquiv_C',
      Polynomial.map_C, hfibC, lineMap, aeval_C, Polynomial.algebraMap_apply, Polynomial.C_comp]
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.mul_comp, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [shear_apply, shearHom_X_zero, finSuccEquiv_X_zero, Polynomial.map_X, lineMap, aeval_X]
      simp only [Fin.cons_zero, map_one, one_mul, Polynomial.add_comp, Polynomial.C_comp,
        Polynomial.X_comp]
      ring
    · rw [shear_apply, shearHom_X_succ, map_add, map_mul, finSuccEquiv_X_succ, finSuccEquiv_X_zero,
        finSuccEquiv_C', Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_X, hfib, hfibC, lineMap, aeval_X]
      simp only [Fin.cons_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp, Polynomial.C_sub, Polynomial.C_mul]
      ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fibre_eq

end Fibre

/-- **GEO-AFF.** The affine presentation holds over every infinite field. -/
theorem infiniteFieldAffineMonicFibre : InfiniteFieldAffineMonicFibreStatement := by
  intro K _ _ n f f' M hM hfM hf'M hf0 hrel
  letI : Field (MvPolynomial (Fin (n + 1)) K ⧸ M) := Ideal.Quotient.field M
  obtain ⟨x, hx⟩ : ∃ x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K ⧸ M,
      ∀ i, x i = Ideal.Quotient.mk M (X i) := ⟨fun i => Ideal.Quotient.mk M (X i), fun _ => rfl⟩
  have hπ : ∀ g : MvPolynomial (Fin (n + 1)) K,
      Ideal.Quotient.mk M g = eval x (map (algebraMap K _) g) := by
    intro g
    rw [MvPolynomial.eval_map]
    induction g using MvPolynomial.induction_on with
    | C c =>
      rw [eval₂_C, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    | add p q hp hq =>
      simp only [map_add, eval₂_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, eval₂_mul, hp, eval₂_X, hx]
  have hx' : eval x (map (algebraMap K _) f') ≠ 0 := by
    rw [← hπ]
    exact fun h0 => hf'M (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  obtain ⟨a, ha, hcop⟩ := exists_direction hrel hf0 hx'
  refine ⟨shear a, ⟨(eval a (lcPoly f))⁻¹, inv_ne_zero ha, monic_finSuccEquiv_C_mul_shear a ha⟩, ?_⟩
  rw [fibre_eq a M x hx f, fibre_eq a M x hx f']
  exact hcop.map (Polynomial.compRingHom (Polynomial.X - Polynomial.C (x 0)))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.infiniteFieldAffineMonicFibre

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
