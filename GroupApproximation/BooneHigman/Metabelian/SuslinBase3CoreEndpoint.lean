import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CoreLift
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2, congruence core: the family endpoint

Lane `bh-met-91h`.  Target: `SuslinBase3GlobalStatement` (`SuslinBase3Endpoint.lean`).

**Proved here.**
* `suslinBase3Core_global_of_core`: `SuslinBase3CoreGlobalStatement → SuslinBase3GlobalStatement`,
  by the residue-field reduction `suslinBase3Core_stabLocal_of_core` at `n = 2`.  It uses
  nothing about the two families: the reduction holds over every commutative ring.
* `suslinBase3Core_localHorrocks`, `Envelope.suslinBase3Core_finitelyPresentedMetabelian`:
  the downstream companions with `SuslinBase3GlobalStatement` replaced by the core.

**Truth check (LOUD).**
* The residual is logically EQUIVALENT to the target, not weaker: it is a special case of it
  (`suslinBase3Core_core_of_global`), and `suslinBase3Core_iff_global` records both directions.
  Since the target is true, no true residual with a proved reduction can be logically weaker.
* It is strictly SMALLER IN PROOF CONTENT.  It asks for `diag(σ_𝔪, 1) ∈ E_3(A_𝔪[X])` only for
  normalized `σ ∈ SL_2(A[X])` that are moreover `≡ 1 mod 𝔪 A[X]`.  The whole residue-field
  part of the problem — `SL_2(κ[X]) = E_2(κ[X])` for `κ = A/𝔪` by the Euclidean algorithm, the
  lift of the factorization to `A[X]` and its normalization at `X = 0` — is discharged here.
* It is TRUE.  Truth witness only: `suslinBase3Core_global_of_localCaseFamily`, from Suslin's
  local case.  It is NOT asserted for general `A` (the cusp `k[t², t³]` has `NK₁ ≠ 0`, and a
  normalized non-elementary class there can be taken `≡ 1` modulo the cusp maximal ideal, by the
  reduction above run in reverse).
* **Remaining gap.**  The congruence core: stably, a normalized `σ ∈ SL_2(A[X])` with
  `σ ≡ 1 mod 𝔪` becomes elementary over `A_𝔪[X]`.  Its diagonal entries are `1 + (𝔪-terms)`,
  which are NOT units of `A_𝔪[X]` in general (e.g. `1 + tX`, `t ∈ 𝔪`), so no Whitehead-lemma
  shortcut applies; this is the `K₁`-regularity core over the regular local ring `A_𝔪`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual family Statement**: the congruence core at rank `2` for the two families,
under the `SL = E` hypothesis of `SuslinBase3GlobalStatement`.  TRUE
(`suslinBase3Core_global_of_localCaseFamily`) and EQUIVALENT to `SuslinBase3GlobalStatement`
(`suslinBase3Core_iff_global`), but strictly smaller in proof content. -/
def SuslinBase3CoreGlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinBase3CoreStab (Chain.CharPPoly p k) 2) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3CoreStab (Chain.SIntPoly m k) 2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3CoreGlobalStatement

/-- **The reduction**: the congruence core gives `SuslinBase3GlobalStatement`. -/
theorem suslinBase3Core_global_of_core (h : SuslinBase3CoreGlobalStatement) :
    SuslinBase3GlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3Core_stabLocal_of_core (by decide) (h.1 p k hk hA),
    fun m k hA ↦ suslinBase3Core_stabLocal_of_core (by decide) (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_global_of_core

/-- **The converse (LOUD equivalence)**: the core is a special case of the target. -/
theorem suslinBase3Core_core_of_global (h : SuslinBase3GlobalStatement) :
    SuslinBase3CoreGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinBase3Core_core_of_stabLocal (h.1 p k hk hA),
    fun m k hA ↦ suslinBase3Core_core_of_stabLocal (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_core_of_global

/-- The congruence core and the target are equivalent. -/
theorem suslinBase3Core_iff_global :
    SuslinBase3CoreGlobalStatement ↔ SuslinBase3GlobalStatement :=
  ⟨suslinBase3Core_global_of_core, suslinBase3Core_core_of_global⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_iff_global

/-- The congruence core gives the rank-3 base of R2. -/
theorem suslinBase3Core_indBase_of_core (h : SuslinBase3CoreGlobalStatement) :
    SuslinR2IndBaseStatement :=
  suslinBase3_indBase_of_global (suslinBase3Core_global_of_core h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_indBase_of_core

/-- **Truth witness only**: Suslin's local case gives the congruence core. -/
theorem suslinBase3Core_global_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinBase3CoreGlobalStatement :=
  suslinBase3Core_core_of_global (suslinBase3_global_of_localCaseFamily h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_global_of_localCaseFamily

/-- Local Horrocks from the `ℤ[1/m]` coordinate Statement and the congruence core. -/
theorem suslinBase3Core_localHorrocks (hc : SuslinR1FinIntCoordStatement)
    (h : SuslinBase3CoreGlobalStatement) : SuslinLocalHorrocksStatement :=
  suslinBase3_localHorrocks hc (suslinBase3Core_global_of_core h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_localHorrocks

end Absorption

namespace Envelope

/-- **The frontier root with `SuslinBase3GlobalStatement` replaced** by the congruence core
`SuslinBase3CoreGlobalStatement`. -/
theorem suslinBase3Core_finitelyPresentedMetabelian
    (hc : Absorption.SuslinR1FinIntCoordStatement)
    (h : Absorption.SuslinBase3CoreGlobalStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  suslinBase3_finitelyPresentedMetabelian hc (Absorption.suslinBase3Core_global_of_core h)
    hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinBase3Core_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
