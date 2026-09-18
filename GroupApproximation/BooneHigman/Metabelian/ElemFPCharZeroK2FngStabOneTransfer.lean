import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngStabOneReduce
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngStabOneMat
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngStabOneSym
import GroupApproximation.Algebra.ElementaryPaddingInjective
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# `czK2FngTorus_StabOneStatement`, proved outright (lane bh-met-92z, 5)

Fix `i ≠ k` in `Fin 3`.  Let `σ : Fin 3 ↪ Fin 4` be `0 ↦ i, 1 ↦ k, 2 ↦ 3`, and let
`τ : Fin 2 ↪ Fin 3` be `0 ↦ i, 1 ↦ k`.  Then `σ` carries `stab St_2` to `stab St_3` through `τ`,
and it carries `X`, `Y` of `St_3` to `X`, `Y` of `St_4` supported on `{i, k}`.

The word `T` of `czK2FngStabOne_TriStatement` is `σ y₀` for a word `y₀ ∈ St_3(ℤ[1/1])`.
* `czK2FngStabOne_mat` gives `y' ∈ H X Y X Y H` with `padMat y' = padMat y₀`.  So
  `u = y'⁻¹ y₀ ∈ K₂(3)`, and `K₂(3) ≤ ⟪sym⟫` (`czK2FngStabOne_k2_le_normalClosure`).
* `sym ∈ stab St_2`, so `σ sym = stab (τ z) ∈ stab K₂(3)`.  That subgroup is central in `St_4`,
  hence normal, so `σ u ∈ stab K₂(3)`.
* `T = σ y' · σ u`, and `σ y' ∈ H X Y X Y H`, so `T ∈ H X Y X Y H` (`czK2FngStabOne_tri`).

With `czK2FngStabOne_stabOne_of_tri`, this proves `czK2FngTorus_StabOneStatement`
(`czK2FngStabOne_stabOne`).  No hypothesis and no literature input.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

local notation "R₁" => Localization.Away ((1 : ℕ) : ℤ)

/-- The index map `0 ↦ i, 1 ↦ k, 2 ↦ 3` from `Fin 3` into `Fin 4`. -/
def czK2FngStabOne_sigmaFun (i k : Fin 3) : Fin (2 + 1) → Fin (3 + 1) :=
  ![i.castSucc, k.castSucc, Fin.last 3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigmaFun

/-- The index map `0 ↦ i, 1 ↦ k` from `Fin 2` into `Fin 3`. -/
def czK2FngStabOne_tauFun (i k : Fin 3) : Fin 2 → Fin 3 := ![i, k]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_tauFun

theorem czK2FngStabOne_sigmaFun_injective :
    ∀ i k : Fin 3, k ≠ i → Function.Injective (czK2FngStabOne_sigmaFun i k) := by
  decide +kernel

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigmaFun_injective

theorem czK2FngStabOne_tauFun_injective :
    ∀ i k : Fin 3, k ≠ i → Function.Injective (czK2FngStabOne_tauFun i k) := by
  decide +kernel

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_tauFun_injective

/-- `σ : Fin 3 ↪ Fin 4`. -/
def czK2FngStabOne_sigma (i k : Fin 3) (hki : k ≠ i) : Fin (2 + 1) ↪ Fin (3 + 1) :=
  ⟨czK2FngStabOne_sigmaFun i k, czK2FngStabOne_sigmaFun_injective i k hki⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma

/-- `τ : Fin 2 ↪ Fin 3`. -/
def czK2FngStabOne_tau (i k : Fin 3) (hki : k ≠ i) : Fin 2 ↪ Fin 3 :=
  ⟨czK2FngStabOne_tauFun i k, czK2FngStabOne_tauFun_injective i k hki⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_tau

/-- `σ ∘ stab = stab ∘ τ`. -/
theorem czK2FngStabOne_sigma_stab (i k : Fin 3) (hki : k ≠ i) (g : St 2 R₁) :
    indexMap (czK2FngStabOne_sigma i k hki) (stab 2 R₁ g) =
      stab 3 R₁ (indexMap (czK2FngStabOne_tau i k hki) g) := by
  have he : Fin.castSuccEmb.trans (czK2FngStabOne_sigma i k hki) =
      (czK2FngStabOne_tau i k hki).trans Fin.castSuccEmb := by
    refine Function.Embedding.ext fun p => ?_
    fin_cases p <;> rfl
  have h : indexMap (R := R₁) (Fin.castSuccEmb.trans (czK2FngStabOne_sigma i k hki)) g =
      indexMap ((czK2FngStabOne_tau i k hki).trans Fin.castSuccEmb) g := by
    rw [he]
  rw [indexMap_trans, indexMap_trans] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_stab

theorem czK2FngStabOne_sigma_padCol2 (i k : Fin 3) (hki : k ≠ i) (a b : R₁) :
    indexMap (czK2FngStabOne_sigma i k hki)
        (padCol (Pi.single 0 a + Pi.single 1 b : Fin 2 → R₁)) =
      padCol (Pi.single i a + Pi.single k b) := by
  rw [padCol_add, padCol_add, map_mul, padCol_single, padCol_single, padCol_single,
    padCol_single, indexMap_x, indexMap_x]
  all_goals rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padCol2

theorem czK2FngStabOne_sigma_padRow2 (i k : Fin 3) (hki : k ≠ i) (a b : R₁) :
    indexMap (czK2FngStabOne_sigma i k hki)
        (padRow (Pi.single 0 a + Pi.single 1 b : Fin 2 → R₁)) =
      padRow (Pi.single i a + Pi.single k b) := by
  rw [padRow_add, padRow_add, map_mul, padRow_single, padRow_single, padRow_single,
    padRow_single, indexMap_x, indexMap_x]
  all_goals rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padRow2

theorem czK2FngStabOne_sigma_padCol1 (i k : Fin 3) (hki : k ≠ i) (a : R₁) :
    indexMap (czK2FngStabOne_sigma i k hki) (padCol (Pi.single 0 a : Fin 2 → R₁)) =
      padCol (Pi.single i a) := by
  rw [padCol_single, padCol_single, indexMap_x]
  all_goals rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padCol1

theorem czK2FngStabOne_sigma_padRow1 (i k : Fin 3) (hki : k ≠ i) (a : R₁) :
    indexMap (czK2FngStabOne_sigma i k hki) (padRow (Pi.single 0 a : Fin 2 → R₁)) =
      padRow (Pi.single i a) := by
  rw [padRow_single, padRow_single, indexMap_x]
  all_goals rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padRow1

theorem czK2FngStabOne_fin2_eta (v : Fin 2 → R₁) :
    v = Pi.single 0 (v 0) + Pi.single 1 (v 1) :=
  (Finset.univ_sum_single v).symm.trans (Fin.sum_univ_two fun p => Pi.single p (v p))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_fin2_eta

theorem czK2FngStabOne_sigma_padCol (i k : Fin 3) (hki : k ≠ i) (v : Fin 2 → R₁) :
    indexMap (czK2FngStabOne_sigma i k hki) (padCol v) =
      padCol (Pi.single i (v 0) + Pi.single k (v 1)) := by
  rw [← czK2FngStabOne_sigma_padCol2 i k hki (v 0) (v 1), ← czK2FngStabOne_fin2_eta v]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padCol

theorem czK2FngStabOne_sigma_padRow (i k : Fin 3) (hki : k ≠ i) (v : Fin 2 → R₁) :
    indexMap (czK2FngStabOne_sigma i k hki) (padRow v) =
      padRow (Pi.single i (v 0) + Pi.single k (v 1)) := by
  rw [← czK2FngStabOne_sigma_padRow2 i k hki (v 0) (v 1), ← czK2FngStabOne_fin2_eta v]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_padRow

/-- `stab` reflects `K₂`, since identity padding is injective. -/
theorem czK2FngStabOne_mem_K2_of_stab {R : Type*} [Ring R] {n : ℕ} {w : St n R}
    (h : stab n R w ∈ K2 (Fin (n + 1)) R) : w ∈ K2 (Fin n) R := by
  apply surjStab_mem_K2_of_padMat_eq_one
  have h1 : ElementaryPadding.padHom (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) (padMat w) = 1 := by
    rw [← czTriOff_padMat_indexMap]
    exact padMat_of_mem_K2 h
  exact ElementaryPadding.padHom_injective _ (h1.trans
    (map_one (ElementaryPadding.padHom (R := R) (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)))).symm)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_mem_K2_of_stab

/-- `stab K₂(3)` is central in `St_4`, hence normal. -/
theorem czK2FngStabOne_normal : ((K2 (Fin 3) R₁).map (stab 3 R₁)).Normal :=
  ⟨fun u hu g => by
    have hc := Subgroup.mem_center_iff.mp
      (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.map_stab_K2_le_center hu) g
    rw [hc, mul_inv_cancel_right]
    exact hu⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_normal

/-- `σ ⟪sym⟫ ≤ stab K₂(3)`. -/
theorem czK2FngStabOne_closure_le_comap (i k : Fin 3) (hki : k ≠ i) :
    Subgroup.normalClosure {czK2FngStabOne_sym} ≤
      ((K2 (Fin 3) R₁).map (stab 3 R₁)).comap (indexMap (czK2FngStabOne_sigma i k hki)) := by
  haveI := czK2FngStabOne_normal
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ rfl
  refine Subgroup.mem_comap.mpr ?_
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp czK2FngStabOne_sym_mem_range_stab
  rw [← hz, czK2FngStabOne_sigma_stab]
  refine Subgroup.mem_map.mpr ⟨indexMap (czK2FngStabOne_tau i k hki) z, ?_, rfl⟩
  apply czK2FngStabOne_mem_K2_of_stab
  rw [← czK2FngStabOne_sigma_stab i k hki z, hz]
  exact indexMap_mem_K2 _ czK2FngStabOne_sym_mem_K2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_closure_le_comap

/-- `σ` carries `H X Y X Y H` of `St_3` into `H X Y X Y H` of `St_4`. -/
theorem czK2FngStabOne_sigma_mem (i k : Fin 3) (hki : k ≠ i) {y : St (2 + 1) R₁}
    (hy : SurjStabLengthMem y) :
    SurjStabLengthMem (indexMap (czK2FngStabOne_sigma i k hki) y) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, czK2FngStabOne_sigma_stab,
    czK2FngStabOne_sigma_stab, czK2FngStabOne_sigma_padCol, czK2FngStabOne_sigma_padRow,
    czK2FngStabOne_sigma_padCol, czK2FngStabOne_sigma_padRow]
  exact ⟨_, _, _, _, _, _, rfl⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sigma_mem

/-- The `St_3`-supported rank-two words of `St_4(ℤ[1/1])` lie in `H X Y X Y H`. -/
theorem czK2FngStabOne_tri : czK2FngStabOne_TriStatement := by
  intro i k hki α δ ζ η β γ
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : St (2 + 1) R₁, y₀ =
      padRow (Pi.single 0 α + Pi.single 1 δ : Fin 2 → R₁) *
        padCol (Pi.single 0 ζ + Pi.single 1 η : Fin 2 → R₁) *
        padRow (Pi.single 0 β : Fin 2 → R₁) * padCol (Pi.single 0 γ : Fin 2 → R₁) :=
    ⟨_, rfl⟩
  obtain ⟨y', hy', hpad⟩ := czK2FngStabOne_mat y₀
  have hK : y'⁻¹ * y₀ ∈ K2 (Fin (2 + 1)) R₁ := by
    apply surjStab_mem_K2_of_padMat_eq_one
    rw [map_mul, ← hpad, ← map_mul padMat, inv_mul_cancel, map_one]
  have hN := Subgroup.mem_comap.mp (czK2FngStabOne_closure_le_comap i k hki
    (czK2FngStabOne_k2_le_normalClosure hK))
  obtain ⟨h₀, -, hh₀⟩ := Subgroup.mem_map.mp hN
  have hmem := czK2FngStabOne_sigma_mem i k hki hy'
  have hsplit : indexMap (czK2FngStabOne_sigma i k hki) y₀ =
      indexMap (czK2FngStabOne_sigma i k hki) y' * stab 3 R₁ h₀ := by
    rw [hh₀, ← map_mul (indexMap (czK2FngStabOne_sigma i k hki)), mul_inv_cancel_left]
  have hfin : SurjStabLengthMem (indexMap (czK2FngStabOne_sigma i k hki) y₀) := by
    rw [hsplit]
    exact surjStabLength_mem_mul_stab hmem h₀
  rw [hy₀, map_mul, map_mul, map_mul, czK2FngStabOne_sigma_padRow2,
    czK2FngStabOne_sigma_padCol2, czK2FngStabOne_sigma_padRow1,
    czK2FngStabOne_sigma_padCol1] at hfin
  exact hfin

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_tri

/-- **`czK2FngTorus_StabOneStatement`, outright.** -/
theorem czK2FngStabOne_stabOne : czK2FngTorus_StabOneStatement :=
  czK2FngStabOne_stabOne_of_tri czK2FngStabOne_tri

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_stabOne

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
