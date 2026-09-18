import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticPatch
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationStatement
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin dilation, analytic half, part 5: the localized Statement

Lane `bh-met-76`.  Target: `SuslinDilationGeneratedStatement` (`SuslinDilationStatement.lean`).

**Isolated Statement.**  `SuslinDilationAnalyticStatement` has the same hypotheses and asks, for
a normalized `τ ∈ SL_N(A[X])` and a maximal ideal `𝔪`, only for some `a ∉ 𝔪` such that the
image of `τ` in `GL_N(A_a[X])` is elementary (`SuslinDilationAnalyticLocallyElementary`).
There is no second variable and no Quillen matrix: this is exactly what local Horrocks over
`A_𝔪[X]` followed by clearing finitely many denominators produces.

* **Reduction** (`suslinDilationGenerated_of_analytic`): for `N ≥ 3`, Suslin's dilation lemma
  (`suslinDilAn_dilation`, `SuslinDilationAnalyticPatch.lean`) applied to `B = A[X]`,
  `S = A_a[X]`, `s = a` and the Quillen matrix `σ = τ(X + Y) τ(X)⁻¹` (which has `σ(Y = 0) = 1`)
  gives `σ(X + a^k Y) τ(X)⁻¹ ∈ E_N(A[X][Y])`, i.e. `a^k ∈ Q(τ)`, and `a^k ∉ 𝔪`
  (`suslinDilAn_quillen_of_map`).  So `τ` is itself one of the generators.
* **Converse** (`suslinDilationAnalyticStatement_of_generated`): generators give `a ∉ 𝔪` with
  `a ∈ Q(τ)` (`suslinDilation_quillen_of_mem_closure`); substituting `Y ↦ -X/a` over `A_a`
  turns `τ(X + aY) τ(X)⁻¹` into `τ(0) τ(X)⁻¹ = τ(X)⁻¹`, so `τ ∈ E_N(A_a[X])`.

**Truth check.**  TRUE, by Suslin's theorem (A. A. Suslin, 1977): for the two coefficient
families and `N ≥ 3`, `SL_N(A[X]) = E_N(A[X])`, so `a = 1` works.

**LOUD: only equivalent.**  Both implications are proved here, so the isolated Statement is
logically EQUIVALENT to `SuslinDilationGeneratedStatement`, not strictly weaker.  What is removed
is the whole analytic half of the dilation principle (the commutator/dilation estimate).  What
remains open is local Horrocks over `A_𝔪[X]` and clearing denominators from `A_𝔪` to some `A_a`;
the local-ring fact `SL_N(R) = E_N(R)` (row reduction) is NOT proved in this lane.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Substitution

variable {A S : Type*} [CommRing A] [CommRing S]

theorem suslinDilAn_constantCoeff_comp_shift (a : A) :
    (Polynomial.constantCoeff (R := Polynomial A)).comp (suslinLocalGlobalShift a) =
      (Polynomial.constantCoeff (R := Polynomial A)).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_C]
  · simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_X, map_add,
      Polynomial.constantCoeff_apply (Polynomial.C (Polynomial.C a) * Polynomial.X),
      Polynomial.coeff_mul_X_zero, add_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_constantCoeff_comp_shift

theorem suslinDilAn_mapMap_comp_shift (f : A →+* S) (a : A) :
    (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp (suslinLocalGlobalShift a) =
      (suslinLocalGlobalShift (f a)).comp (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, suslinLocalGlobalShift_C, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
  · simp only [RingHom.comp_apply, suslinLocalGlobalShift_X, Polynomial.coe_mapRingHom,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_mapMap_comp_shift

theorem suslinDilAn_dilate_C (c : A) :
    suslinDilAnDilate (Polynomial.C c) = suslinLocalGlobalDilate c :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_dilate_C

/-- `Y ↦ -v X` over `S`, where `v` inverts `f(a)`, kills the shift `X ↦ X + aY`. -/
theorem suslinDilAn_eval_comp_shift (f : A →+* S) {a : A} {v : S} (hv : f a * v = 1) :
    (Polynomial.eval₂RingHom (Polynomial.mapRingHom f)
        (Polynomial.C (-v) * Polynomial.X)).comp (suslinLocalGlobalShift a) =
      ((Polynomial.C : S →+* Polynomial S).comp f).comp (Polynomial.constantCoeff (R := A)) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.constantCoeff_apply,
      Polynomial.coeff_C_zero]
  · simp only [RingHom.comp_apply]
    have hC : Polynomial.C (f a) * Polynomial.C v = 1 := by
      rw [← Polynomial.C_mul, hv, Polynomial.C_1]
    rw [Polynomial.constantCoeff_apply, Polynomial.coeff_X_zero, map_zero, map_zero,
      suslinLocalGlobalShift_X, map_add, map_mul, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_mapRingHom,
      Polynomial.map_X, Polynomial.map_C, Polynomial.C_neg]
    linear_combination (-Polynomial.X) * hC

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_eval_comp_shift

theorem suslinDilAn_eval_comp_C (f : A →+* S) (w : Polynomial S) :
    (Polynomial.eval₂RingHom (Polynomial.mapRingHom f) w).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) =
      Polynomial.mapRingHom f :=
  RingHom.ext fun p ↦ by
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_eval_comp_C

theorem suslinDilAn_away_surj (a : A) :
    ∀ c : Localization.Away a, ∃ (t : ℕ) (b : A),
      c * algebraMap A (Localization.Away a) a ^ t = algebraMap A (Localization.Away a) b := by
  intro c
  obtain ⟨⟨b, x⟩, h⟩ := IsLocalization.surj (Submonoid.powers a) c
  obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).1 x.2
  refine ⟨t, b, ?_⟩
  rw [← map_pow, ht]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_away_surj

theorem suslinDilAn_away_ker (a : A) :
    ∀ b : A, algebraMap A (Localization.Away a) b = 0 → ∃ n : ℕ, a ^ n * b = 0 := by
  intro b hb
  obtain ⟨⟨x, hx⟩, h⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) b).1 hb
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  exact ⟨n, h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_away_ker

end Substitution

section Quillen

variable {A S : Type*} [CommRing A] [CommRing S] {N : ℕ}

/-- **The analytic half** (`N ≥ 3`): if `f : A → S` satisfies `hsurj`, `hker` (e.g.
`A → A_a`) and `f(τ) ∈ E_N(S[X])`, then `a^k ∈ Q(τ)` for some `k`.  No normalization of `τ`
is needed: the Quillen matrix `τ(X + Y) τ(X)⁻¹` always has value `1` at `Y = 0`. -/
theorem suslinDilAn_quillen_of_map (hN : 2 < N) (f : A →+* S) (a : A)
    (hsurj : ∀ c : S, ∃ (t : ℕ) (b : A), c * f a ^ t = f b)
    (hker : ∀ b : A, f b = 0 → ∃ n : ℕ, a ^ n * b = 0)
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hτ : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom f) τ ∈
      elementaryGroup (Fin N) (Polynomial S)) :
    ∃ k : ℕ, SuslinLocalGlobalQuillen τ (a ^ k) := by
  have hσ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := Polynomial A))
      (elementaryMatrixUnitMap (ι := Fin N) (suslinLocalGlobalShift (1 : A)) τ *
        (elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) τ)⁻¹) = 1 := by
    rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
      suslinDilAn_constantCoeff_comp_shift, mul_inv_cancel]
  have hsh := suslinDilAn_mapMap_comp_shift f (1 : A)
  rw [map_one f] at hsh
  have h1 := elementaryGroup_map_le (ι := Fin N) (suslinLocalGlobalShift (1 : S))
    (Subgroup.mem_map_of_mem _ hτ)
  rw [suslinLocalGlobal_map_map, ← hsh, ← suslinLocalGlobal_map_map] at h1
  have h2 := elementaryGroup_map_le (ι := Fin N)
    (Polynomial.C : Polynomial S →+* Polynomial (Polynomial S)) (Subgroup.mem_map_of_mem _ hτ)
  rw [suslinLocalGlobal_map_map, ← Polynomial.mapRingHom_comp_C,
    ← suslinLocalGlobal_map_map] at h2
  have hσ : elementaryMatrixUnitMap (ι := Fin N)
      (Polynomial.mapRingHom (Polynomial.mapRingHom f))
      (elementaryMatrixUnitMap (ι := Fin N) (suslinLocalGlobalShift (1 : A)) τ *
        (elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) τ)⁻¹) ∈
      elementaryGroup (Fin N) (Polynomial (Polynomial S)) := by
    rw [map_mul, map_inv]
    exact mul_mem h1 (inv_mem h2)
  obtain ⟨k, hk⟩ := suslinDilAn_dilation (Polynomial.mapRingHom f) (Polynomial.C a) hN
    (suslinDilAn_surj_poly f a hsurj) (suslinDilAn_ker_poly f a hker) _ hσ0 hσ
  refine ⟨k, ?_⟩
  rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map, ← Polynomial.C_pow,
    suslinDilAn_dilate_C, suslinLocalGlobalDilate_comp_shift, mul_one,
    suslinLocalGlobalDilate_comp_C] at hk
  exact hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_quillen_of_map

/-- Conversely, if `f(a) v = 1`, `τ(0) = 1` and `a ∈ Q(τ)`, then `f(τ) ∈ E_N(S[X])`
(substitute `Y ↦ -vX`). -/
theorem suslinDilAn_map_mem_of_quillen (f : A →+* S) {a : A} {v : S} (hv : f a * v = 1)
    {τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)}
    (hτ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1)
    (hQ : SuslinLocalGlobalQuillen τ a) :
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom f) τ ∈
      elementaryGroup (Fin N) (Polynomial S) := by
  unfold SuslinLocalGlobalQuillen at hQ
  have h := elementaryGroup_map_le (ι := Fin N)
    (Polynomial.eval₂RingHom (Polynomial.mapRingHom f) (Polynomial.C (-v) * Polynomial.X))
    (Subgroup.mem_map_of_mem _ hQ)
  rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
    suslinDilAn_eval_comp_shift f hv, suslinDilAn_eval_comp_C, ← suslinLocalGlobal_map_map, hτ0,
    map_one, one_mul] at h
  exact inv_mem_iff.1 h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_map_mem_of_quillen

end Quillen

/-- For every normalized `τ ∈ SL_N(A[X])` and maximal ideal `𝔪`, some `a ∉ 𝔪` makes the image
of `τ` in `GL_N(A_a[X])` elementary. -/
def SuslinDilationAnalyticLocallyElementary (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ a ∉ 𝔪,
          elementaryMatrixUnitMap (ι := Fin N)
              (Polynomial.mapRingHom (algebraMap A (Localization.Away a))) τ ∈
            elementaryGroup (Fin N) (Polynomial (Localization.Away a))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinDilationAnalyticLocallyElementary

theorem suslinDilAn_generated_of_locallyElementary {A : Type*} [CommRing A] {N : ℕ}
    (hN : 3 ≤ N) (h : SuslinDilationAnalyticLocallyElementary A N) :
    SuslinDilationGeneratedQuillen A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨a, ha𝔪, ha⟩ := h τ hdet h0 𝔪 h𝔪
  obtain ⟨k, hk⟩ := suslinDilAn_quillen_of_map (by omega) (algebraMap A (Localization.Away a)) a
    (suslinDilAn_away_surj a) (suslinDilAn_away_ker a) τ ha
  have hmem : τ ∈ {σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A) |
      ∃ a ∉ 𝔪, SuslinLocalGlobalQuillen σ a} :=
    ⟨a ^ k, fun hk𝔪 ↦ ha𝔪 (h𝔪.isPrime.mem_of_pow_mem k hk𝔪), hk⟩
  exact Subgroup.subset_closure hmem

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_generated_of_locallyElementary

theorem suslinDilAn_locallyElementary_of_generated {A : Type*} [CommRing A] {N : ℕ}
    (hN : 3 ≤ N) (h : SuslinDilationGeneratedQuillen A N) :
    SuslinDilationAnalyticLocallyElementary A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨a, ha𝔪, ha⟩ :=
    suslinDilation_quillen_of_mem_closure (by omega) h𝔪.isPrime (h τ hdet h0 𝔪 h𝔪)
  obtain ⟨v, hv⟩ :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).exists_right_inv
  exact ⟨a, ha𝔪, suslinDilAn_map_mem_of_quillen (algebraMap A (Localization.Away a)) hv h0 ha⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_locallyElementary_of_generated
