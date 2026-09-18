import GroupApproximation.BooneHigman.Metabelian.SuslinWeaveInduction
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks by a rank-interleaved induction: the family endpoint

Lane `bh-met-90x`.  Target: `SuslinLocalHorrocksStatement` (the gap `hH` of
`Envelope.hmClosed_finitelyPresentedMetabelian_of_six`).

**Proved here.**  `suslinWeave_localHorrocks`: from
* `SuslinR1FinIntCoordStatement` (lane `bh-met-90r`: the coordinate-change Statement for
  `ℤ[1/m][s_1,…,s_k]`), and
* `SuslinR2IndBaseStatement` (lane `bh-met-90q`: the block form of R2 at rank `3` only),

the per-ring induction `suslinWeave_local` gives R1 and R2 at every rank `N ≥ 3` for both
families.  The char `p` coordinate Statement is PROVED (Nagata over `ZMod p`,
`suslinR1Fin_coord_of_field`).  Injectivity of `A → A_𝔪` is `suslinR2Ind_injective_charP` /
`suslinR2Ind_injective_sInt`.  The family Statements `SuslinHorrocksR1Statement` and
`SuslinHorrocksR2Statement` are then CONSTRUCTED (`suslinWeave_R1`, `suslinWeave_R2`), not
assumed, and `suslinR1_localHorrocks_of_R1_R2` closes the target.
`Envelope.suslinWeave_finitelyPresentedMetabelian` replaces `hH` by `hc`, `h3`.

**No hidden circularity.**  The endpoint hypotheses are exactly `hc` and `h3`; neither
`SuslinHorrocksR1Statement`, `SuslinHorrocksR2Statement`, `SuslinR2BlockStatement` nor
`SuslinR1FiniteStatement` appears as a hypothesis anywhere in this lane.  `hc` and `h3` are
defined in `SuslinR1FinEndpoint.lean`, `SuslinR2IndFamily.lean` as concrete per-rank
Statements (`SuslinR1FinCoordLocal`, `SuslinR2BlockLocal`), not as family wrappers.

**LOUD: logical strength.**  `hc ∧ h3` is EQUIVALENT to `SuslinLocalHorrocksStatement`, not
strictly weaker: the converse `suslinWeave_inputs_of_localHorrocks` is proved here (both
conjuncts follow from the patching Statement, which follows from local Horrocks).  So both
inputs are TRUE (by Suslin's theorem, via local Horrocks).  What is strictly removed is proof
content: the char `p` coordinate change (Nagata), all ranks `N ≥ 4` of R2 (the induction), all
of R1 given the coordinate change (finiteness, local Horrocks row step, Quillen patching,
dilation), and the local-global bookkeeping.  What remains:
1. the `ℤ[1/m]` monic trick (a unit leading coefficient after an automorphism of `A[X]` and an
   elementary factor), a global statement with no localization;
2. the rank-3 `K₁`-regularity core: `diag(σ, 1) = τ_𝔪 F` with `σ ∈ SL_2(A_𝔪[X])`, `σ(0) = 1`,
   gives `τ_𝔪 ∈ E_3`, for both families.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The char `p` family**: R2 (block form) and R1 at every rank `N ≥ 3`, from the base. -/
theorem suslinWeave_charP (h3 : SuslinR2IndBaseStatement) (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 1 ≤ k) (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') :
    ∀ N : ℕ, 3 ≤ N → SuslinR2BlockLocal (Chain.CharPPoly p k) N ∧
      SuslinR1MonicLocal (Chain.CharPPoly p k) N :=
  suslinWeave_local (suslinR2Ind_injective_charP p k) hA
    (fun _ hN ↦ suslinR1Fin_coord_of_field (K := ZMod p) (n := k) (by omega))
    (h3.1 p k hk hA)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_charP

/-- **The `ℤ[1/m]` family**: R2 (block form) and R1 at every rank `N ≥ 3`, from the base and
the `ℤ` coordinate Statement. -/
theorem suslinWeave_sInt (hc : SuslinR1FinIntCoordStatement) (h3 : SuslinR2IndBaseStatement)
    (m k : ℕ) (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') :
    ∀ N : ℕ, 3 ≤ N → SuslinR2BlockLocal (Chain.SIntPoly m k) N ∧
      SuslinR1MonicLocal (Chain.SIntPoly m k) N :=
  suslinWeave_local (suslinR2Ind_injective_sInt m k) hA (fun N hN ↦ hc m k N hA hN)
    (h3.2 m k hA)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_sInt

/-- **R1 for the families, constructed** from `hc` and `h3`. -/
theorem suslinWeave_R1 (hc : SuslinR1FinIntCoordStatement) (h3 : SuslinR2IndBaseStatement) :
    SuslinHorrocksR1Statement :=
  ⟨fun p _ k N hk hA hN ↦ (suslinWeave_charP h3 p k hk hA N hN).2,
    fun m k N hA hN ↦ (suslinWeave_sInt hc h3 m k hA N hN).2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_R1

/-- **The block form of R2 for the families, constructed** from `hc` and `h3`. -/
theorem suslinWeave_block (hc : SuslinR1FinIntCoordStatement)
    (h3 : SuslinR2IndBaseStatement) : SuslinR2BlockStatement :=
  ⟨fun p _ k N hk hA hN ↦ (suslinWeave_charP h3 p k hk hA N hN).1,
    fun m k N hA hN ↦ (suslinWeave_sInt hc h3 m k hA N hN).1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_block

/-- **R2 for the families, constructed** from `hc` and `h3`. -/
theorem suslinWeave_R2 (hc : SuslinR1FinIntCoordStatement) (h3 : SuslinR2IndBaseStatement) :
    SuslinHorrocksR2Statement :=
  suslinR2_statement_of_block (suslinWeave_block hc h3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_R2

/-- **The target**: local Horrocks for the families, from `hc` and `h3` alone. -/
theorem suslinWeave_localHorrocks (hc : SuslinR1FinIntCoordStatement)
    (h3 : SuslinR2IndBaseStatement) : SuslinLocalHorrocksStatement :=
  suslinR1_localHorrocks_of_R1_R2 (suslinWeave_R1 hc h3) (suslinWeave_R2 hc h3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_localHorrocks

/-- **Truth, and LOUD equivalence**: local Horrocks gives both inputs back. -/
theorem suslinWeave_inputs_of_localHorrocks (h : SuslinLocalHorrocksStatement) :
    SuslinR1FinIntCoordStatement ∧ SuslinR2IndBaseStatement :=
  ⟨suslinR1Fin_intCoord_of_localHorrocks h,
    ⟨fun p _ k hk hA ↦ suslinWeave_blockLocal_of_normalized
      ((suslinPatching_of_localHorrocks h).1 p k 3 hk hA le_rfl),
    fun m k hA ↦ suslinWeave_blockLocal_of_normalized
      ((suslinPatching_of_localHorrocks h).2 m k 3 hA le_rfl)⟩⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_inputs_of_localHorrocks

/-- The two inputs together are equivalent to local Horrocks. -/
theorem suslinWeave_iff_localHorrocks :
    (SuslinR1FinIntCoordStatement ∧ SuslinR2IndBaseStatement) ↔
      SuslinLocalHorrocksStatement :=
  ⟨fun h ↦ suslinWeave_localHorrocks h.1 h.2, suslinWeave_inputs_of_localHorrocks⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinWeave_iff_localHorrocks

end Absorption

namespace Envelope

/-- **The frontier root with `hH` replaced** by the `ℤ[1/m]` coordinate Statement and the
rank-3 base of R2. -/
theorem suslinWeave_finitelyPresentedMetabelian
    (hc : Absorption.SuslinR1FinIntCoordStatement)
    (h3 : Absorption.SuslinR2IndBaseStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six (Absorption.suslinWeave_localHorrocks hc h3)
    hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinWeave_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
