import GroupApproximation.BooneHigman.Metabelian.SuslinR2Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# Stabilizer step (R2), part 4: the family Statements

Lane `bh-met-90k`.  `SuslinR2BlockStatement` is `SuslinR2BlockLocal` for the two coefficient
families, under the hypotheses of `SuslinHorrocksR2Statement` (lane `bh-met-90j`).

* `suslinR2_statement_of_block`: **the reduction** `SuslinR2BlockStatement →
  SuslinHorrocksR2Statement` (column clearing and normalization, `SuslinR2Core.lean`).
* `suslinR2_block_of_statement`: the converse.  LOUD: the two are EQUIVALENT.  The block
  Statement is strictly smaller in proof content, not logically weaker.
* `suslinR2_block_of_localCaseFamily`: TRUE, from `SuslinLocalCaseFamilyStatement` (Suslin).
* `suslinR2_localHorrocks_of_R1_block`: the gap `SuslinLocalHorrocksStatement` from R1 and the
  block Statement.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The family block Statement**: `SuslinR2BlockLocal` for the two coefficient families. -/
def SuslinR2BlockStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinR2BlockLocal (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinR2BlockLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR2BlockStatement

/-- **The reduction**: the family block Statement gives `SuslinHorrocksR2Statement`. -/
theorem suslinR2_statement_of_block (h : SuslinR2BlockStatement) :
    SuslinHorrocksR2Statement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR2_stabLocal_of_blockLocal (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR2_stabLocal_of_blockLocal (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_statement_of_block

/-- The converse (LOUD: equivalent): `SuslinHorrocksR2Statement` gives the block Statement. -/
theorem suslinR2_block_of_statement (h : SuslinHorrocksR2Statement) :
    SuslinR2BlockStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR2_blockLocal_of_stabLocal (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR2_blockLocal_of_stabLocal (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_block_of_statement

/-- **Truth witness**: the family local case gives the block Statement. -/
theorem suslinR2_block_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinR2BlockStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR2_blockLocal_of_localCase (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR2_blockLocal_of_localCase (h.2 m k N hA hN)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_block_of_localCaseFamily

/-- **The gap from R1 and the block Statement**: `SuslinLocalHorrocksStatement`. -/
theorem suslinR2_localHorrocks_of_R1_block (h1 : SuslinHorrocksR1Statement)
    (h2 : SuslinR2BlockStatement) : SuslinLocalHorrocksStatement :=
  suslinR1_localHorrocks_of_R1_R2 h1 (suslinR2_statement_of_block h2)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_localHorrocks_of_R1_block

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
