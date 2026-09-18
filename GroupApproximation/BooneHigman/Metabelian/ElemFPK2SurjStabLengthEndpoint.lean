import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabLengthReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, length reduction: endpoint over `ℤ[1/m]` (lane bh-met-86)

`SurjStabLengthRankTwoStatement` is the remaining gap.  For `m > 0` and `n ≥ 4`, it says
every rank-two word `Y_w X_c Y_{e_i β} X_{e_i γ}` of `St_{n+1}(ℤ[1/m])` lies in
`S = H X Y X Y H` (`SurjStabLengthMem`).

## Reduction (proved here, no further inputs)

1. `Y X Y X ⊆ S`.  Move the middle row to `e_i β` by `stab h` (Euclid,
   `surjStabGauss_away_reach_single`), using `H`-conjugation invariance
   (`surjStabLength_mem_word_of_conj`).  Then split off the part of the last column away from
   `i` (`surjStabLength_mem_word_single`).
2. `S · X ⊆ S` (`surjStabLength_mem_mul_padCol_of_word`), hence `S = St_{n+1}` by generator
   induction (`surjStabLength_mem_all_of_col`).
3. Every `x`, in particular every `x ∈ K₂`, has the Gauss form with `z = 1`.  Hence
   `SurjStabGaussFormStatement`, `SurjStabConjTripleStatement` and surjective stability
   `K₂(n+1) ≤ stab K₂(n)` follow.

## Truth check (LOUD)

The gap is TRUE, but it is NOT weaker than the target in truth content.  It is equivalent
(`surjStabLength_rankTwo_of_all`, `surjStabLength_all_of_rankTwo`) to
`SurjStabLengthAllStatement`, i.e. `St_{n+1}(ℤ[1/m]) = H X Y X Y H`.  That set equality
implies the target.  Conversely it follows from surjective stability together with the
matrix-level decomposition `E_{n+1} = H X Y X Y E_n`.  To get that decomposition, choose
`w'` with `r - t w'` unimodular (`sr(ℤ[1/m]) ≤ 2 ≤ n`), set `w = r - t w'`, and solve
`w · c = t - 1`.  The remaining block lies in `SL_n = E_n`.

So the gap is stronger per element than the target.  It is equivalent, modulo classical
facts, to the target plus that decomposition.  It is strictly smaller in proof content: the
generator induction, the `X`/`Y`/`H` absorptions, the Euclid move and the disjoint-support
splitting are all discharged here.  What remains is only the rank-two collapse
`Y X Y_{e_i} X_{e_i} → H X Y X Y H`, i.e. the Steinberg-level length reduction.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- The gap: rank-two words `Y_w X_c Y_{e_i β} X_{e_i γ}` lie in `H X Y X Y H`. -/
def SurjStabLengthRankTwoStatement : Prop :=
  ∀ m n : ℕ, 0 < m → 4 ≤ n → ∀ (w c : Fin n → Localization.Away (m : ℤ)) (i : Fin n)
    (β γ : Localization.Away (m : ℤ)),
    SurjStabLengthMem (padRow w * padCol c * padRow (Pi.single i β) * padCol (Pi.single i γ))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabLengthRankTwoStatement

/-- `St_{n+1}(ℤ[1/m]) = H X Y X Y H`. -/
def SurjStabLengthAllStatement : Prop :=
  ∀ m n : ℕ, 0 < m → 4 ≤ n → ∀ y : St (n + 1) (Localization.Away (m : ℤ)), SurjStabLengthMem y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabLengthAllStatement

/-- `Y X Y X ⊆ S` over `ℤ[1/m]`, from the gap. -/
theorem surjStabLength_away_mem_word (h : SurjStabLengthRankTwoStatement) {m n : ℕ}
    (hm : 0 < m) (hn : 4 ≤ n) (w c w' c' : Fin n → Localization.Away (m : ℤ)) :
    SurjStabLengthMem (padRow w * padCol c * padRow w' * padCol c') := by
  obtain ⟨i, β, hr⟩ := surjStabGauss_away_reach_single (m := m) (by omega : 0 < n) w'
  obtain ⟨g, hg⟩ := hr
  refine surjStabLength_mem_word_of_conj g w c w' c' ?_
  rw [hg]
  exact surjStabLength_mem_word_single _ _ i β _ (fun w₁ c₁ => h m n hm hn w₁ c₁ i β _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_away_mem_word

/-- The gap gives `St_{n+1}(ℤ[1/m]) = H X Y X Y H`. -/
theorem surjStabLength_all_of_rankTwo (h : SurjStabLengthRankTwoStatement) :
    SurjStabLengthAllStatement := fun _ _ hm hn y =>
  surjStabLength_mem_all_of_col (fun _ i a hs =>
    surjStabLength_mem_mul_padCol_of_word (surjStabLength_away_mem_word h hm hn) hs
      (Pi.single i a)) y

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_all_of_rankTwo

/-- Trivial converse (LOUD: the gap is equivalent to `SurjStabLengthAllStatement`). -/
theorem surjStabLength_rankTwo_of_all (h : SurjStabLengthAllStatement) :
    SurjStabLengthRankTwoStatement := fun m n hm hn _ _ _ _ _ => h m n hm hn _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_rankTwo_of_all

/-- Main endpoint: the gap implies `SurjStabGaussFormStatement`. -/
theorem surjStabLength_gaussForm_of_rankTwo (h : SurjStabLengthRankTwoStatement) :
    SurjStabGaussFormStatement := fun m n hm hn x _ =>
  surjStabLength_gaussForm_of_mem (surjStabLength_all_of_rankTwo h m n hm hn x)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_gaussForm_of_rankTwo

theorem surjStabLength_conjTriple_of_rankTwo (h : SurjStabLengthRankTwoStatement) :
    SurjStabConjTripleStatement :=
  surjStabConjTriple_of_surjStabGaussForm (surjStabLength_gaussForm_of_rankTwo h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_conjTriple_of_rankTwo

/-- Surjective `K₂` stability over `ℤ[1/m]`, `n ≥ 4`, from the gap. -/
theorem surjStabLength_k2SurjStab_of_rankTwo (h : SurjStabLengthRankTwoStatement) :
    ∀ m n : ℕ, 0 < m → 4 ≤ n → K2 (Fin (n + 1)) (Localization.Away (m : ℤ)) ≤
      (K2 (Fin n) (Localization.Away (m : ℤ))).map (stab n (Localization.Away (m : ℤ))) :=
  charZeroK2SurjStab_of_conjTriple (surjStabLength_conjTriple_of_rankTwo h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_k2SurjStab_of_rankTwo

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
