import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabCollapseWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, rank-two collapse: endpoint over `ℤ[1/m]` (lane bh-met-89)

`SurjStabCollapseTriStatement` is the remaining gap.  For `m > 0`, `n ≥ 4` and `k ≠ i`, it
says that the word
`Y_{e_i α + e_k δ} · X_{e_i ζ + e_k η} · Y_{e_i β} · X_{e_i γ}` of `St_{n+1}(ℤ[1/m])` lies in
`S = H X Y X Y H` (`SurjStabLengthMem`).  This word lives in the copy of `St_3` on the
indices `{i, k, last}`.

## Reduction (proved here): `SurjStabLengthRankTwoStatement` from the gap

Take the word `Y_w X_c Y_{e_i β} X_{e_i γ}`.
1. Euclid away from `i` (`surjStabCollapse_away_reach`).  An element `h` fixing the row and
   column `e_i` moves `w` to `e_i (w i) + e_k δ` with `k ≠ i`.  Conjugation by `stab h` keeps
   the last two factors (`surjStabCollapse_mem_word_of_fix`).
2. The column is cut down to `{i, k}` by the disjoint-support absorption
   (`surjStabCollapse_mem_word_split`).
Hence `SurjStabLengthAllStatement`, `SurjStabGaussFormStatement`, and surjective stability
`K₂(n+1) ≤ stab K₂(n)` over `ℤ[1/m]` follow from the gap
(`surjStabCollapse_k2SurjStab_of_tri`).

## Truth check (LOUD)

The gap is TRUE: it is a special case of `SurjStabLengthRankTwoStatement`, which is true.
Indeed `St_{n+1}(ℤ[1/m]) = H X Y X Y H` follows from van der Kallen surjective stability
(`sr(ℤ[1/m]) ≤ 2`, `n ≥ 3`) plus the matrix decomposition in `ElemFPK2SurjStabLengthEndpoint`.

As Statements, the gap and `SurjStabLengthRankTwoStatement` imply each other
(`surjStabCollapse_rankTwo_of_tri`, and the specialization `surjStabCollapse_tri_of_rankTwo`).
So the gap is NOT weaker in truth content; it still carries the whole Steinberg-level length
reduction.  Per instance it is a strict special case: `w` and `c` have support in `{i, k}`
instead of all of `Fin n`, so the word lives in an `St_3` with six scalar parameters.  It is
strictly smaller in proof content: the Euclid step avoiding `i` and the disjoint-support
splitting are discharged here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- **Gap**: the `St_3`-supported rank-two words lie in `H X Y X Y H`. -/
def SurjStabCollapseTriStatement : Prop :=
  ∀ m n : ℕ, 0 < m → 4 ≤ n → ∀ i k : Fin n, k ≠ i →
    ∀ α δ ζ η β γ : Localization.Away (m : ℤ),
      SurjStabLengthMem (padRow (Pi.single i α + Pi.single k δ) *
        padCol (Pi.single i ζ + Pi.single k η) * padRow (Pi.single i β) *
        padCol (Pi.single i γ))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabCollapseTriStatement

/-- **Endpoint**: the rank-two statement from the `St_3` gap. -/
theorem surjStabCollapse_rankTwo_of_tri (h : SurjStabCollapseTriStatement) :
    SurjStabLengthRankTwoStatement := by
  intro m n hm hn w c i β γ
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨k0, hk0⟩ := exists_ne i
  obtain ⟨k, δ, hki, g, hg, hwg⟩ := surjStabCollapse_away_reach (m := m) i k0 hk0 w
  refine surjStabCollapse_mem_word_of_fix hg w c β γ ?_
  rw [hwg]
  refine surjStabCollapse_mem_word_split _ i k hki ?_ _ _ _ ?_
  · intro l hli hlk
    rw [Pi.add_apply, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlk, add_zero]
  · exact h m n hm hn i k hki _ _ _ _ β γ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_rankTwo_of_tri

/-- LOUD converse: the gap is the specialization of the rank-two statement. -/
theorem surjStabCollapse_tri_of_rankTwo (h : SurjStabLengthRankTwoStatement) :
    SurjStabCollapseTriStatement := fun m n hm hn i k _ α δ ζ η β γ =>
  h m n hm hn (Pi.single i α + Pi.single k δ) (Pi.single i ζ + Pi.single k η) i β γ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_tri_of_rankTwo

/-- `St_{n+1}(ℤ[1/m]) = H X Y X Y H`, from the gap. -/
theorem surjStabCollapse_all_of_tri (h : SurjStabCollapseTriStatement) :
    SurjStabLengthAllStatement :=
  surjStabLength_all_of_rankTwo (surjStabCollapse_rankTwo_of_tri h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_all_of_tri

/-- The Gauss form statement, from the gap. -/
theorem surjStabCollapse_gaussForm_of_tri (h : SurjStabCollapseTriStatement) :
    SurjStabGaussFormStatement :=
  surjStabLength_gaussForm_of_rankTwo (surjStabCollapse_rankTwo_of_tri h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_gaussForm_of_tri

/-- Surjective `K₂` stability over `ℤ[1/m]`, `n ≥ 4`, from the gap. -/
theorem surjStabCollapse_k2SurjStab_of_tri (h : SurjStabCollapseTriStatement) :
    ∀ m n : ℕ, 0 < m → 4 ≤ n → K2 (Fin (n + 1)) (Localization.Away (m : ℤ)) ≤
      (K2 (Fin n) (Localization.Away (m : ℤ))).map (stab n (Localization.Away (m : ℤ))) :=
  surjStabLength_k2SurjStab_of_rankTwo (surjStabCollapse_rankTwo_of_tri h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_k2SurjStab_of_tri

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
