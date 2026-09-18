import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3FamEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2 for the two families: endpoint of lane `bh-met-91u`

* `SuslinCongLocGlobalStatement`: `SuslinBase3CongGlobalStatement` with the core
  `SuslinBase3CongPowStab A 2` replaced by `SuslinCongLocPowStab A` (only the normalized
  `σ ≡ 1 mod 𝔪^N` whose localized image is OUTSIDE the `GL₂(A_𝔪[X])`-normal closure of
  `E₂(A_𝔪[X])`, the rank-one unipotents and all `ψ(SL₂(A))`).
* `suslinCongLoc_congGlobal_of_locGlobal` (**the reduction**): it uses the family hypothesis
  `SL₃(A) = E₃(A)` AT LEVEL `k` only (non-circular), Suslin normality of `E₃` and the rank-one
  lemma (both PROVED in the repo).
* `suslinCongLoc_locGlobal_of_famGlobal`: the residual of lane `bh-met-91p` implies this one.
* `suslinCongLoc_locGlobal_iff_congGlobal`: **LOUD: EQUIVALENT** to
  `SuslinBase3CongGlobalStatement`; strictly smaller only in PROOF CONTENT.
* Downstream: `SuslinBase3CoreGlobalStatement`, `SuslinBase3GlobalStatement`,
  `SuslinR2IndBaseStatement`.

**Truth check / closure (LOUD).**  No closure: the residual is K1-regularity of the regular local
rings `A_𝔪` in rank 2 (plus one stabilization), outside the discharged class.  True on the
families exactly when `SuslinBase3CongGlobalStatement` is.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual global Statement**: the deep-congruence core only outside the local
normal-closure class, for the two families, under the level-`k` family hypothesis. -/
def SuslinCongLocGlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinCongLocPowStab (Chain.CharPPoly p k)) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinCongLocPowStab (Chain.SIntPoly m k)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinCongLocGlobalStatement

/-- **The reduction**, using `SL₃ = E₃` at level `k`. -/
theorem suslinCongLoc_congGlobal_of_locGlobal (h : SuslinCongLocGlobalStatement) :
    SuslinBase3CongGlobalStatement :=
  ⟨fun p _ k hk hA ↦
      suslinCongLoc_powStab_of_locPowStab (hA (2 + 1) (by norm_num)) (h.1 p k hk hA),
    fun m k hA ↦
      suslinCongLoc_powStab_of_locPowStab (hA (2 + 1) (by norm_num)) (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_congGlobal_of_locGlobal

/-- The residual of lane `bh-met-91p` implies this residual. -/
theorem suslinCongLoc_locGlobal_of_famGlobal (h : SuslinBase3FamGlobalStatement) :
    SuslinCongLocGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinCongLoc_locPowStab_of_famPowStab (h.1 p k hk hA),
    fun m k hA ↦ suslinCongLoc_locPowStab_of_famPowStab (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_locGlobal_of_famGlobal

/-- The trivial converse. -/
theorem suslinCongLoc_locGlobal_of_congGlobal (h : SuslinBase3CongGlobalStatement) :
    SuslinCongLocGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinCongLoc_locPowStab_of_powStab (h.1 p k hk hA),
    fun m k hA ↦ suslinCongLoc_locPowStab_of_powStab (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_locGlobal_of_congGlobal

/-- **LOUD: the residual is equivalent** to `SuslinBase3CongGlobalStatement` (smaller only in
proof content). -/
theorem suslinCongLoc_locGlobal_iff_congGlobal :
    SuslinCongLocGlobalStatement ↔ SuslinBase3CongGlobalStatement :=
  ⟨suslinCongLoc_congGlobal_of_locGlobal, suslinCongLoc_locGlobal_of_congGlobal⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_locGlobal_iff_congGlobal

/-- The residual gives the congruence core for both families. -/
theorem suslinCongLoc_coreGlobal_of_locGlobal (h : SuslinCongLocGlobalStatement) :
    SuslinBase3CoreGlobalStatement :=
  suslinBase3Cong_coreGlobal_of_congGlobal (suslinCongLoc_congGlobal_of_locGlobal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_coreGlobal_of_locGlobal

/-- The residual gives the stabilized base for both families. -/
theorem suslinCongLoc_global_of_locGlobal (h : SuslinCongLocGlobalStatement) :
    SuslinBase3GlobalStatement :=
  suslinBase3Cong_global_of_congGlobal (suslinCongLoc_congGlobal_of_locGlobal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_global_of_locGlobal

/-- The residual gives the rank-3 base of R2. -/
theorem suslinCongLoc_indBase_of_locGlobal (h : SuslinCongLocGlobalStatement) :
    SuslinR2IndBaseStatement :=
  suslinBase3Cong_indBase_of_congGlobal (suslinCongLoc_congGlobal_of_locGlobal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_indBase_of_locGlobal

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
