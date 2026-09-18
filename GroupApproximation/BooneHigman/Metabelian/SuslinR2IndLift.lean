import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndDilate
import Mathlib.RingTheory.Localization.Integral
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank induction for R2, part 2: lifting local matrices by a dilation

Lane `bh-met-90q`.  **The key lemma** is `suslinR2Ind_mem_of_localCase`.  It removes the type
mismatch that blocked a rank induction in lane `bh-met-90k` (see `SuslinR2Statement.lean`):
there, the block `σ` of `τ_𝔪 F` lives over `A_𝔪[X]` and is not the image of a matrix over
`A[X]`.

**Lemma.**  Suppose `A → A_𝔪` is injective (e.g. `A` a domain) and `SuslinLocalCaseStatement A n`
holds.  Then every `σ ∈ SL_n(A_𝔪[X])` with `σ(0) = 1` is in `E_n(A_𝔪[X])`.

**Proof.**  Choose a common denominator `s ∉ 𝔪` of the entries of `σ` and `σ⁻¹`, so that
`s σ` and `s σ⁻¹` are images of matrices over `A[X]`.  The dilation lift
(`suslinR2Ind_lift_poly`) gives matrices `P, Q` over `A[X]` with `P ↦ σ(s X)` and
`Q ↦ σ⁻¹(s X)`.  Injectivity of `A[X] → A_𝔪[X]` gives `P Q = Q P = 1` and `det P = 1`, and
`P(0) = 1` by construction.  The local case, applied to `P` at `𝔪`, gives `σ(s X) ∈ E_n`.  Since
`s` is a unit in `A_𝔪`, the dilation is undone (`suslinR2Ind_mem_of_dilate`).

LOUD: this shows that, for `A → A_𝔪` injective, the local case at rank `n` is EQUIVALENT to its
τ-free form "every normalized `σ ∈ SL_n(A_𝔪[X])` is elementary".  The τ-free form is not
stronger in this setting.  It is still not a Vorst-type statement: it is proved here only from
the local case, which is the hypothesis `hL`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

section Lift

/-- **Common denominator** of a finite family of polynomials over a localization. -/
theorem suslinR2Ind_common_denom {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [Fintype κ] (g : κ → S[X]) :
    ∃ b ∈ M, ∃ q : κ → R[X], ∀ k, (q k).map (algebraMap R S) = C (algebraMap R S b) * g k := by
  classical
  choose c hc hq using fun k ↦ IsLocalization.integerNormalization_spec M (g k)
  refine ⟨∏ k, c k, M.prod_mem fun k _ ↦ hc k,
    fun k ↦ C (∏ l ∈ Finset.univ.erase k, c l) * IsLocalization.integerNormalization M (g k),
    fun k ↦ ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, hq k,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), map_mul, C_mul, mul_assoc]
  congr 1
  ext n
  rw [coeff_smul, coeff_C_mul, Algebra.smul_def]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_common_denom

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The entries of a normalized matrix at `X = 0`. -/
theorem suslinR2Ind_coeff_zero (σ : (Matrix ι ι R[X])ˣ)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := R)) σ = 1) (i j : ι) :
    ((σ : Matrix ι ι R[X]) i j).coeff 0 = (1 : Matrix ι ι R) i j := by
  have h : ((elementaryMatrixUnitMap (Polynomial.constantCoeff (R := R)) σ :
      (Matrix ι ι R)ˣ) : Matrix ι ι R) i j = ((1 : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j := by
    rw [h0]
  change Polynomial.constantCoeff ((σ : Matrix ι ι R[X]) i j) = _ at h
  rw [Polynomial.constantCoeff_apply, Units.val_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_coeff_zero

/-- A ring map preserves the entries of the identity matrix. -/
theorem suslinR2Ind_one_apply_map {S : Type*} [CommRing S] (f : R →+* S) (i j : ι) :
    (1 : Matrix ι ι S) i j = f ((1 : Matrix ι ι R) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_one_apply_map

/-- **Matrix dilation lift.**  If `q_{ij} ↦ f(s) σ_{ij}` and `σ(0) = 1`, then the matrix
`P_{ij} = X q_{ij}.divX(s X) + δ_{ij}` over `R[X]` lifts the dilate `σ(f(s) X)` and has
`P(0) = 1`. -/
theorem suslinR2Ind_lift_matrix {S : Type*} [CommRing S] (f : R →+* S)
    (σ : (Matrix ι ι S[X])ˣ)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := S)) σ = 1)
    (s : R) (q : ι → ι → R[X])
    (hq : ∀ i j, (q i j).map f = C (f s) * (σ : Matrix ι ι S[X]) i j) :
    ∃ P : Matrix ι ι R[X],
      (mapRingHom f).mapMatrix P = (compRingHom (C (f s) * X)).mapMatrix (σ : Matrix ι ι S[X]) ∧
        ∀ i j, (P i j).coeff 0 = (1 : Matrix ι ι R) i j := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix ι ι R[X], ∀ i j,
      P i j = X * ((q i j).divX.comp (C s * X)) + C ((1 : Matrix ι ι R) i j) :=
    ⟨fun i j ↦ X * ((q i j).divX.comp (C s * X)) + C ((1 : Matrix ι ι R) i j),
      fun _ _ ↦ rfl⟩
  refine ⟨P, ?_, fun i j ↦ ?_⟩
  · ext i j
    change (P i j).map f = ((σ : Matrix ι ι S[X]) i j).comp (C (f s) * X)
    rw [hP]
    refine suslinR2Ind_lift_poly f (q i j) ((σ : Matrix ι ι S[X]) i j) s _ (hq i j) ?_
    rw [suslinR2Ind_coeff_zero σ h0, suslinR2Ind_one_apply_map f]
  · rw [hP, coeff_add, coeff_X_mul_zero, coeff_C_zero, zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_lift_matrix

/-- Injectivity of a coefficient map on polynomial matrices. -/
theorem suslinR2Ind_mapMatrix_injective {S : Type*} [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) (M N : Matrix ι ι R[X])
    (h : (mapRingHom f).mapMatrix M = (mapRingHom f).mapMatrix N) : M = N := by
  ext i j
  exact Polynomial.map_injective f hf (congrFun (congrFun h i) j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_mapMatrix_injective

end Lift

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
