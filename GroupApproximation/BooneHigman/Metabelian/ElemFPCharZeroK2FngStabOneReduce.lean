import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabCollapseEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import GroupApproximation.Meta.AxiomGuard

/-!
# `czK2FngTorus_StabOneStatement`: rank-three length reduction over `ℤ[1/1]` (lane bh-met-92z, 1)

The repository chain `SurjStabLengthMem → SurjStabGaussForm → SurjStabFactorDisj →
SurjStabConjTriple → stab K₂` is stated for all `n ≥ 4` there. At the element level, though,
nothing in it needs `n ≥ 4`. This file runs it at `n = 3`, `R = ℤ[1/1]`, and shows that the
`St_3`-supported word statement `czK2FngStabOne_TriStatement` gives

* `czK2FngStabOne_le_map_of_tri`: `K₂(4, ℤ[1/1]) ≤ stab K₂(3, ℤ[1/1])`, and hence
* `czK2FngStabOne_stabOne_of_tri`: `czK2FngTorus_StabOneStatement`.

`czK2FngStabOne_TriStatement` is not a residual. It is proved outright as
`czK2FngStabOne_tri` in `ElemFPCharZeroK2FngStabOneTransfer`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

local notation "R₁" => Localization.Away ((1 : ℕ) : ℤ)

/-- The `St_3`-supported rank-two words of `St_4(ℤ[1/1])` lie in `H X Y X Y H`. -/
def czK2FngStabOne_TriStatement : Prop :=
  ∀ i k : Fin 3, k ≠ i → ∀ α δ ζ η β γ : R₁,
    SurjStabLengthMem (padRow (Pi.single i α + Pi.single k δ) *
      padCol (Pi.single i ζ + Pi.single k η) * padRow (Pi.single i β) *
      padCol (Pi.single i γ))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_TriStatement

/-- Rank-two words with a single row `e_i β`, from the `St_3`-supported ones. -/
theorem czK2FngStabOne_rankTwo_of_tri (h : czK2FngStabOne_TriStatement)
    (w c : Fin 3 → R₁) (i : Fin 3) (β γ : R₁) :
    SurjStabLengthMem (padRow w * padCol c * padRow (Pi.single i β) *
      padCol (Pi.single i γ)) := by
  haveI : Nontrivial (Fin 3) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨k0, hk0⟩ := exists_ne i
  obtain ⟨k, δ, hki, g, hg, hwg⟩ := surjStabCollapse_away_reach (m := 1) i k0 hk0 w
  refine surjStabCollapse_mem_word_of_fix hg w c β γ ?_
  rw [hwg]
  refine surjStabCollapse_mem_word_split _ i k hki ?_ _ _ _ ?_
  · intro l hli hlk
    rw [Pi.add_apply, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlk, add_zero]
  · exact h i k hki _ _ _ _ β γ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_rankTwo_of_tri

/-- All words `Y X Y X` of `St_4(ℤ[1/1])` lie in `H X Y X Y H`. -/
theorem czK2FngStabOne_mem_word_of_tri (h : czK2FngStabOne_TriStatement)
    (w c w' c' : Fin 3 → R₁) :
    SurjStabLengthMem (padRow w * padCol c * padRow w' * padCol c') := by
  obtain ⟨i, β, hr⟩ := surjStabGauss_away_reach_single (m := 1) (by omega : 0 < 3) w'
  obtain ⟨g, hg⟩ := hr
  refine surjStabLength_mem_word_of_conj g w c w' c' ?_
  rw [hg]
  exact surjStabLength_mem_word_single _ _ i β _
    (fun w₁ c₁ => czK2FngStabOne_rankTwo_of_tri h w₁ c₁ i β _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_mem_word_of_tri

/-- `St_4(ℤ[1/1]) = H X Y X Y H`. -/
theorem czK2FngStabOne_all_of_tri (h : czK2FngStabOne_TriStatement)
    (y : St (3 + 1) R₁) : SurjStabLengthMem y :=
  surjStabLength_mem_all_of_col (fun _ i a hs =>
    surjStabLength_mem_mul_padCol_of_word (czK2FngStabOne_mem_word_of_tri h) hs
      (Pi.single i a)) y

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_all_of_tri

/-- Surjective stability `K₂(4, ℤ[1/1]) ≤ stab K₂(3, ℤ[1/1])`. -/
theorem czK2FngStabOne_le_map_of_tri (h : czK2FngStabOne_TriStatement) :
    K2 (Fin (3 + 1)) R₁ ≤ (K2 (Fin 3) R₁).map (stab 3 R₁) := by
  haveI : IsDomain R₁ :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 one_ne_zero))
  refine surjStab_k2_le_map_of_conjTriple fun x hx => ?_
  obtain ⟨w, hF⟩ := surjStabLength_gaussForm_of_mem (czK2FngStabOne_all_of_tri h x)
  obtain ⟨i, β, hr⟩ := surjStabGauss_away_reach_single (m := 1) (by omega : 0 < 3) w
  exact surjStabFactor_conjTriple_of_disj hx
    (surjStabGauss_factorDisj_of_single hx (surjStabGauss_form_of_reach hF hr))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_le_map_of_tri

/-- The torus residual from the `St_3`-supported word statement. -/
theorem czK2FngStabOne_stabOne_of_tri (h : czK2FngStabOne_TriStatement) :
    czK2FngTorus_StabOneStatement :=
  czK2FngTorus_stabOne_of_le_map (czK2FngStabOne_le_map_of_tri h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_stabOne_of_tri

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
