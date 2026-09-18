import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank induction for R2, part 5: the family block Statement from its rank-3 base and R1

Lane `bh-met-90q`.  Target: `SuslinR2BlockStatement` (`SuslinR2Family.lean`).

**Proved here.**
* `suslinR2Ind_blockLocal_of_base`: suppose `A → A_𝔪` is injective for every maximal `𝔪`.
  Then R1 at all ranks `≥ 3`, together with `SuslinR2BlockLocal A 3`, gives
  `SuslinR2BlockLocal A N` for all `N ≥ 3`.  The induction step is
  `BlockLocal(n) + R1(n) ⟹ LocalCase(n) ⟹ BlockLocal(n + 1)`: the first arrow is by repo
  lemmas, the second by `suslinR2Ind_blockLocal_succ`.
* Both families have injective `A → A_𝔪`.  `CharPPoly p k` is a domain.  `SIntPoly m k` is a
  domain if `m ≠ 0` and the zero ring if `m = 0`.
* `suslinR2Ind_block_of_R1_base`: `SuslinHorrocksR1Statement → SuslinR2IndBaseStatement →
  SuslinR2BlockStatement`.
* `suslinR2Ind_localHorrocks_of_R1_base`: the gap `SuslinLocalHorrocksStatement` from R1 and
  the rank-3 base alone.  It replaces `suslinR2_localHorrocks_of_R1_block`, whose R2 input was
  needed at every rank `N ≥ 3`.

**LOUD: what remains.**  `SuslinR2IndBaseStatement` is `SuslinR2BlockStatement` at `N = 3`
only.
* It is IMPLIED by `SuslinR2BlockStatement` (`suslinR2Ind_base_of_block`).
* Conversely, it gives `SuslinR2BlockStatement` only TOGETHER WITH R1
  (`SuslinHorrocksR1Statement`, open, lane `bh-met-90r`), which is an extra hypothesis here.
* So it is strictly smaller in proof content: one rank instead of all.  It is not claimed to be
  logically strictly weaker, since both are true for the families.
* Content: for normalized `τ ∈ SL_3(A[X])`, if `τ_𝔪 F = diag(σ, 1)` (up to reindexing) is
  normalized, then `τ_𝔪 ∈ E_3`.  Here `σ ∈ SL_2(A_𝔪[X])` with `σ(0) = 1`.  This is the
  `K₁`-regularity core at the first stable rank.
* It cannot be reduced one rank further by this method.  The rank-2 local case is FALSE for the
  families: the normalized Cohn matrix is not in `E_2`, see `SuslinR2Statement.lean`.

**LOUD: no stronger statement is asserted.**  The τ-free form "every normalized
`σ ∈ SL_n(A_𝔪[X])` is elementary" appears only as an intermediate step
(`suslinR2Ind_mem_of_localCase`).  There it is DERIVED from the local case at the same rank,
and it is EQUIVALENT to the local case when `A → A_𝔪` is injective.  No τ-free Vorst-type
regularity is assumed.

**Truth check.**  `suslinR2Ind_base_of_localCaseFamily`: the base follows from
`SuslinLocalCaseFamilyStatement`, which is true by Suslin's theorem; this is a truth witness
only, not an input.  Like the block Statement, the base is FALSE for general `A` (the cusp
counterexample), so it is asserted only for the two families.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Rank induction**: R1 at all ranks `≥ 3` and the block form at rank `3` give the block
form at every rank `≥ 3`, when `A → A_𝔪` is injective. -/
theorem suslinR2Ind_blockLocal_of_base {A : Type*} [CommRing A]
    (hf : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (h1 : ∀ N : ℕ, 3 ≤ N → SuslinR1MonicLocal A N) (h3 : SuslinR2BlockLocal A 3) :
    ∀ N : ℕ, 3 ≤ N → SuslinR2BlockLocal A N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact h3
  | succ n hn ih =>
    exact suslinR2Ind_blockLocal_succ (suslinHorrocks_localCase_of_split hn
      (suslinR1_splitLocal_of_monic_stab (h1 n hn) (suslinR2_stabLocal_of_blockLocal ih))) hf

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_blockLocal_of_base

/-- For a domain, `A → A_𝔪` is injective. -/
theorem suslinR2Ind_injective_of_isDomain {A : Type*} [CommRing A] [IsDomain A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    Function.Injective (algebraMap A (Localization.AtPrime 𝔪)) :=
  IsLocalization.injective (Localization.AtPrime 𝔪)
    (@Ideal.primeCompl_le_nonZeroDivisors A _ _ 𝔪 h𝔪.isPrime)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_injective_of_isDomain

/-- `CharPPoly p k → (CharPPoly p k)_𝔪` is injective. -/
theorem suslinR2Ind_injective_charP (p : ℕ) [Fact p.Prime] (k : ℕ)
    (𝔪 : Ideal (Chain.CharPPoly p k)) (h𝔪 : 𝔪.IsMaximal) :
    Function.Injective (algebraMap (Chain.CharPPoly p k) (Localization.AtPrime 𝔪)) :=
  suslinR2Ind_injective_of_isDomain 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_injective_charP

/-- `SIntPoly m k → (SIntPoly m k)_𝔪` is injective.  For `m = 0` the ring is zero, and
otherwise it is a domain. -/
theorem suslinR2Ind_injective_sInt (m k : ℕ) (𝔪 : Ideal (Chain.SIntPoly m k))
    (h𝔪 : 𝔪.IsMaximal) :
    Function.Injective (algebraMap (Chain.SIntPoly m k) (Localization.AtPrime 𝔪)) := by
  by_cases hm : (m : ℤ) = 0
  · have h0 : algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) = 0 :=
      (congrArg (algebraMap ℤ (Localization.Away (m : ℤ))) hm).trans (map_zero _)
    have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (m : ℤ)) (m : ℤ)
    rw [h0, isUnit_zero_iff] at hu
    have hA : (0 : Chain.SIntPoly m k) = 1 := by
      have h := congrArg (MvPolynomial.C (R := Localization.Away (m : ℤ)) (σ := Fin k)) hu
      rwa [map_zero, map_one] at h
    exact fun a b _ ↦ eq_of_zero_eq_one hA a b
  · haveI : IsDomain (Localization.Away (m : ℤ)) := Localization.Away.isDomain hm
    exact suslinR2Ind_injective_of_isDomain 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_injective_sInt

/-- **The rank-3 base**: `SuslinR2BlockLocal` at `N = 3` for the two coefficient families,
under the hypotheses of `SuslinR2BlockStatement`.  LOUD: implied by `SuslinR2BlockStatement`,
and it gives that Statement only together with R1.  FALSE for general `A` (cusp). -/
def SuslinR2IndBaseStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinR2BlockLocal (Chain.CharPPoly p k) 3) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinR2BlockLocal (Chain.SIntPoly m k) 3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR2IndBaseStatement

/-- The block Statement gives its rank-3 base. -/
theorem suslinR2Ind_base_of_block (h : SuslinR2BlockStatement) : SuslinR2IndBaseStatement :=
  ⟨fun p _ k hk hA ↦ h.1 p k 3 hk hA le_rfl, fun m k hA ↦ h.2 m k 3 hA le_rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_base_of_block

/-- **Truth witness**: the family local case (true by Suslin's theorem) gives the base. -/
theorem suslinR2Ind_base_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinR2IndBaseStatement :=
  suslinR2Ind_base_of_block (suslinR2_block_of_localCaseFamily h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_base_of_localCaseFamily

/-- **The reduction**: R1 and the rank-3 base give the family block Statement at every rank
`N ≥ 3`. -/
theorem suslinR2Ind_block_of_R1_base (h1 : SuslinHorrocksR1Statement)
    (h3 : SuslinR2IndBaseStatement) : SuslinR2BlockStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR2Ind_blockLocal_of_base (suslinR2Ind_injective_charP p k)
      (fun N' hN' ↦ h1.1 p k N' hk hA hN') (h3.1 p k hk hA) N hN,
    fun m k N hA hN ↦ suslinR2Ind_blockLocal_of_base (suslinR2Ind_injective_sInt m k)
      (fun N' hN' ↦ h1.2 m k N' hA hN') (h3.2 m k hA) N hN⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_block_of_R1_base

/-- **The gap from R1 and the rank-3 base**: `SuslinLocalHorrocksStatement`. -/
theorem suslinR2Ind_localHorrocks_of_R1_base (h1 : SuslinHorrocksR1Statement)
    (h3 : SuslinR2IndBaseStatement) : SuslinLocalHorrocksStatement :=
  suslinR2_localHorrocks_of_R1_block h1 (suslinR2Ind_block_of_R1_base h1 h3)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_localHorrocks_of_R1_base

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
