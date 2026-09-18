import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndFamily
import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks by a rank-interleaved induction: the per-ring induction

Lane `bh-met-90x`.  The two reductions of lanes `bh-met-90r` (R1 from R2 and the coordinate
Statement) and `bh-met-90q` (R2 from R1 and the rank-3 base) are circular only at the level of
the family Statements.  Per rank they interleave:

* **R1 at rank `N` from R2 at rank `N`** (`suslinWeave_monic`): the block form of R2 at rank `N`
  gives `SuslinR1StabLocal A N` (`suslinR2_stabLocal_of_blockLocal`); with the coordinate
  Statement at rank `N` it makes every normalized `τ` elementary
  (`suslinR1Fin_normalized_of_coord`), hence the finite form of R1
  (`suslinR1Fin_finiteLocal_of_normalized`), hence R1 (`suslinR1_monicLocal_of_finite`).
* **R2 at rank `N + 1` from R1 and R2 at rank `N`**: split Statement
  (`suslinR1_splitLocal_of_monic_stab`), local Horrocks (`suslinHorrocks_localCase_of_split`),
  one rank up (`suslinR2Ind_blockLocal_succ`, needs `A → A_𝔪` injective).

`suslinWeave_local` runs the induction from `SuslinR2BlockLocal A 3`, and gives
`SuslinR2BlockLocal A N ∧ SuslinR1MonicLocal A N` for every `N ≥ 3`.  No family Statement
(`SuslinHorrocksR1Statement`, `SuslinHorrocksR2Statement`, `SuslinR2BlockStatement`,
`SuslinR1FiniteStatement`) is used as a hypothesis: every rank-`N` input is either proved at the
previous step of the induction or is one of the per-rank hypotheses (`SL_N(A) ⊆ E_N(A)`, the
coordinate Statement at rank `N`, injectivity of `A → A_𝔪`, and the base at rank `3`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The per-rank link R2 ⟹ R1**: at rank `N ≥ 3`, with `SL_N(A) ⊆ E_N(A)` and the coordinate
Statement, the block form of R2 gives normalized matrices elementary. -/
theorem suslinWeave_normalized {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (hA : SpecialLinearInElementary A N) (hc : SuslinR1FinCoordLocal A N)
    (hB : SuslinR2BlockLocal A N) : SuslinMonicNormalizedElementary A N :=
  suslinR1Fin_normalized_of_coord hN hA (suslinR2_stabLocal_of_blockLocal hB) hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_normalized

/-- **The per-rank link R2 ⟹ R1**, monic form: R1 (`SuslinR1MonicLocal`) at rank `N`. -/
theorem suslinWeave_monic {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (hA : SpecialLinearInElementary A N) (hc : SuslinR1FinCoordLocal A N)
    (hB : SuslinR2BlockLocal A N) : SuslinR1MonicLocal A N :=
  suslinR1_monicLocal_of_finite
    (suslinR1Fin_finiteLocal_of_normalized hN (suslinWeave_normalized hN hA hc hB))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_monic

/-- **The per-rank link R1 + R2 ⟹ R2 one rank up** (needs `A → A_𝔪` injective). -/
theorem suslinWeave_block_succ {A : Type*} [CommRing A] {n : ℕ} (hn : 3 ≤ n)
    (hf : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (hB : SuslinR2BlockLocal A n) (h1 : SuslinR1MonicLocal A n) :
    SuslinR2BlockLocal A (n + 1) :=
  suslinR2Ind_blockLocal_succ (suslinHorrocks_localCase_of_split hn
    (suslinR1_splitLocal_of_monic_stab h1 (suslinR2_stabLocal_of_blockLocal hB))) hf

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_block_succ

/-- **The rank-interleaved induction.**  If `A → A_𝔪` is injective for every maximal `𝔪`,
`SL_N(A) ⊆ E_N(A)` and the coordinate Statement hold at every rank `N ≥ 3`, then the block form
of R2 at rank `3` gives the block form of R2 and R1 at every rank `N ≥ 3`. -/
theorem suslinWeave_local {A : Type*} [CommRing A]
    (hf : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (hA : ∀ N : ℕ, 3 ≤ N → SpecialLinearInElementary A N)
    (hc : ∀ N : ℕ, 3 ≤ N → SuslinR1FinCoordLocal A N) (h3 : SuslinR2BlockLocal A 3) :
    ∀ N : ℕ, 3 ≤ N → SuslinR2BlockLocal A N ∧ SuslinR1MonicLocal A N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact ⟨h3, suslinWeave_monic le_rfl (hA 3 le_rfl) (hc 3 le_rfl) h3⟩
  | succ n hn ih =>
    have hB : SuslinR2BlockLocal A (n + 1) := suslinWeave_block_succ hn hf ih.1 ih.2
    exact ⟨hB, suslinWeave_monic (by omega) (hA (n + 1) (by omega)) (hc (n + 1) (by omega))
      hB⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_local

/-- The induction also makes every normalized `τ ∈ SL_N(A[X])` elementary, `N ≥ 3`. -/
theorem suslinWeave_normalized_all {A : Type*} [CommRing A]
    (hf : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (hA : ∀ N : ℕ, 3 ≤ N → SpecialLinearInElementary A N)
    (hc : ∀ N : ℕ, 3 ≤ N → SuslinR1FinCoordLocal A N) (h3 : SuslinR2BlockLocal A 3) :
    ∀ N : ℕ, 3 ≤ N → SuslinMonicNormalizedElementary A N := fun N hN ↦
  suslinWeave_normalized hN (hA N hN) (hc N hN) (suslinWeave_local hf hA hc h3 N hN).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_normalized_all

/-- Normalized matrices elementary over `A[X]` give the block form of R2 (trivially). -/
theorem suslinWeave_blockLocal_of_normalized {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinMonicNormalizedElementary A N) : SuslinR2BlockLocal A N :=
  fun τ hdet h0 𝔪 _ _ _ _ _ _ ↦
    elementaryGroup_map_le (ι := Fin N)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
      (Subgroup.mem_map_of_mem _ (h τ hdet h0))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_blockLocal_of_normalized

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
