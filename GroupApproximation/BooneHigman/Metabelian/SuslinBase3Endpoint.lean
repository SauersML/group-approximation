import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Reduce
import GroupApproximation.BooneHigman.Metabelian.SuslinWeaveEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2 from a global `2 × 2` stabilized residual: the family endpoint

Lane `bh-met-91b`.  Target: `SuslinR2IndBaseStatement` (`SuslinR2IndFamily.lean`), the input
`h3` of `Envelope.suslinWeave_finitelyPresentedMetabelian`.

**Proved here.**
* `suslinBase3_indBase_of_global`: `SuslinBase3GlobalStatement → SuslinR2IndBaseStatement`.
  The residual is `SuslinBase3StabLocal A 2` for the two families (`CharPPoly p k`, `k ≥ 1`,
  and `SIntPoly m k`), under the same `SL = E` hypothesis on `A`.  Injectivity of `A → A_𝔪`
  is `suslinR2Ind_injective_charP` / `suslinR2Ind_injective_sInt`.
* `Envelope.suslinBase3_finitelyPresentedMetabelian`: the root with `h3` replaced by
  `SuslinBase3GlobalStatement`.

**Truth check (LOUD).**
* The residual is logically EQUIVALENT to the target, not weaker:
  `suslinBase3_global_of_indBase` proves the converse, and `suslinBase3_iff_indBase` records
  both directions.  Any residual `R` with a proved `R → target` can be at most as weak as the
  target.  A single-family, single-`k` or single-rank piece cannot imply the target as stated.
* It is strictly SMALLER IN PROOF CONTENT.  It asks only that `diag(σ_𝔪, 1) ∈ E_3(A_𝔪[X])`
  for a GLOBAL normalized `σ ∈ SL_2(A[X])`.  The auxiliary elementary factor `F`, the
  coordinate-block bookkeeping and reindexing, and the localized denominators are all removed.
  They are discharged here by the dilation lift (`SuslinBase3Reduce.lean`).
* It is TRUE.  Truth witness only: `suslinBase3_global_of_localCaseFamily`, from Suslin's
  local case.  It is NOT asserted for general `A`.
* **Remaining gap.**  The `K₁`-regularity core at rank `3`: stably, a normalized `2 × 2` block
  over the regular local ring `A_𝔪` is elementary.  No elementary proof of it is available
  here.  No route in these files assumes local Horrocks, R1/R2 or the block Statement.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual family Statement**: the stabilized normalized residual at rank `2` for the
two families, under the `SL = E` hypothesis of `SuslinR2IndBaseStatement`.  It is TRUE
(`suslinBase3_global_of_localCaseFamily`) and EQUIVALENT to `SuslinR2IndBaseStatement`
(`suslinBase3_iff_indBase`). -/
def SuslinBase3GlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinBase3StabLocal (Chain.CharPPoly p k) 2) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3GlobalStatement

/-- **The reduction**: the residual gives the rank-3 base of R2. -/
theorem suslinBase3_indBase_of_global (h : SuslinBase3GlobalStatement) :
    SuslinR2IndBaseStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3_blockLocal_of_stab (n := 2) (h.1 p k hk hA)
      (suslinR2Ind_injective_charP p k),
    fun m k hA ↦ suslinBase3_blockLocal_of_stab (n := 2) (h.2 m k hA)
      (suslinR2Ind_injective_sInt m k)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_indBase_of_global

/-- **The converse (LOUD equivalence)**: the rank-3 base gives the residual back. -/
theorem suslinBase3_global_of_indBase (h : SuslinR2IndBaseStatement) :
    SuslinBase3GlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3_stab_of_blockLocal (n := 2) (h.1 p k hk hA),
    fun m k hA ↦ suslinBase3_stab_of_blockLocal (n := 2) (h.2 m k hA)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_global_of_indBase

/-- The residual and the rank-3 base are equivalent. -/
theorem suslinBase3_iff_indBase : SuslinBase3GlobalStatement ↔ SuslinR2IndBaseStatement :=
  ⟨suslinBase3_indBase_of_global, suslinBase3_global_of_indBase⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_iff_indBase

/-- **Truth witness only**: Suslin's local case gives the residual. -/
theorem suslinBase3_global_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinBase3GlobalStatement :=
  suslinBase3_global_of_indBase (suslinR2Ind_base_of_localCaseFamily h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_global_of_localCaseFamily

/-- Local Horrocks from the `ℤ[1/m]` coordinate Statement and the residual. -/
theorem suslinBase3_localHorrocks (hc : SuslinR1FinIntCoordStatement)
    (h : SuslinBase3GlobalStatement) : SuslinLocalHorrocksStatement :=
  suslinWeave_localHorrocks hc (suslinBase3_indBase_of_global h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_localHorrocks

end Absorption

namespace Envelope

/-- **The frontier root with `h3` replaced** by the global `2 × 2` stabilized residual
`SuslinBase3GlobalStatement`. -/
theorem suslinBase3_finitelyPresentedMetabelian
    (hc : Absorption.SuslinR1FinIntCoordStatement)
    (h : Absorption.SuslinBase3GlobalStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  suslinWeave_finitelyPresentedMetabelian hc (Absorption.suslinBase3_indBase_of_global h)
    hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinBase3_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
