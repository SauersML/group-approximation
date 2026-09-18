import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CoreEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: endpoints of the deep-congruence core

Lane `bh-met-91k`.

`SuslinBase3CongGlobalStatement` is `SuslinBase3CoreGlobalStatement` with the congruence core
`SuslinBase3CoreStab _ 2` replaced by the deep-congruence core `SuslinBase3CongPowStab _ 2`
(`σ ≡ 1 mod 𝔪^N` for a prover-chosen `N` instead of `σ ≡ 1 mod 𝔪`).

* `suslinBase3Cong_coreGlobal_of_congGlobal`: the reduction to the congruence core.
* `suslinBase3Cong_congGlobal_of_coreGlobal`, `suslinBase3Cong_iff_coreGlobal`: LOUD, the two
  family Statements are logically equivalent (see `SuslinBase3CongStatement`); the gain is in
  proof content only: the `SL₂((A/𝔪^N)[X])` layer is proved here, not assumed.
* `suslinBase3Cong_global_of_congGlobal`, `suslinBase3Cong_indBase_of_congGlobal`,
  `suslinBase3Cong_localHorrocks`, `Envelope.suslinBase3Cong_finitelyPresentedMetabelian`: the
  downstream endpoints of `SuslinBase3CoreEndpoint`, rerouted.
* `suslinBase3Cong_congGlobal_of_localCaseFamily`: TRUTH WITNESS only (not a route).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The deep-congruence family Statement**, over the families of `SuslinBase3CoreGlobal`. -/
def SuslinBase3CongGlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinBase3CongPowStab (Chain.CharPPoly p k) 2) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3CongPowStab (Chain.SIntPoly m k) 2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3CongGlobalStatement

/-- **The reduction**: the deep-congruence core gives the congruence core. -/
theorem suslinBase3Cong_coreGlobal_of_congGlobal (h : SuslinBase3CongGlobalStatement) :
    SuslinBase3CoreGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3Cong_core_of_powStab (h.1 p k hk hA),
    fun m k hA ↦ suslinBase3Cong_core_of_powStab (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_coreGlobal_of_congGlobal

/-- **The converse (LOUD equivalence)**, via `N = 1`. -/
theorem suslinBase3Cong_congGlobal_of_coreGlobal (h : SuslinBase3CoreGlobalStatement) :
    SuslinBase3CongGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3Cong_powStab_of_core (h.1 p k hk hA),
    fun m k hA ↦ suslinBase3Cong_powStab_of_core (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_congGlobal_of_coreGlobal

/-- The two family Statements are equivalent. -/
theorem suslinBase3Cong_iff_coreGlobal :
    SuslinBase3CongGlobalStatement ↔ SuslinBase3CoreGlobalStatement :=
  ⟨suslinBase3Cong_coreGlobal_of_congGlobal, suslinBase3Cong_congGlobal_of_coreGlobal⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_iff_coreGlobal

/-- The deep-congruence core gives `SuslinBase3GlobalStatement`. -/
theorem suslinBase3Cong_global_of_congGlobal (h : SuslinBase3CongGlobalStatement) :
    SuslinBase3GlobalStatement :=
  suslinBase3Core_global_of_core (suslinBase3Cong_coreGlobal_of_congGlobal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_global_of_congGlobal

/-- The deep-congruence core gives the rank-3 base of R2. -/
theorem suslinBase3Cong_indBase_of_congGlobal (h : SuslinBase3CongGlobalStatement) :
    SuslinR2IndBaseStatement :=
  suslinBase3Core_indBase_of_core (suslinBase3Cong_coreGlobal_of_congGlobal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_indBase_of_congGlobal

/-- Local Horrocks from the `ℤ[1/m]` coordinate Statement and the deep-congruence core. -/
theorem suslinBase3Cong_localHorrocks (hc : SuslinR1FinIntCoordStatement)
    (h : SuslinBase3CongGlobalStatement) : SuslinLocalHorrocksStatement :=
  suslinBase3Core_localHorrocks hc (suslinBase3Cong_coreGlobal_of_congGlobal h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_localHorrocks

/-- **Truth witness only**: Suslin's local case gives the deep-congruence core. -/
theorem suslinBase3Cong_congGlobal_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinBase3CongGlobalStatement :=
  suslinBase3Cong_congGlobal_of_coreGlobal (suslinBase3Core_global_of_localCaseFamily h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_congGlobal_of_localCaseFamily

end Absorption

namespace Envelope

/-- **The frontier root with `SuslinBase3GlobalStatement` replaced** by the deep-congruence core
`SuslinBase3CongGlobalStatement`. -/
theorem suslinBase3Cong_finitelyPresentedMetabelian
    (hc : Absorption.SuslinR1FinIntCoordStatement)
    (h : Absorption.SuslinBase3CongGlobalStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  suslinBase3Core_finitelyPresentedMetabelian hc
    (Absorption.suslinBase3Cong_coreGlobal_of_congGlobal h) hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinBase3Cong_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
