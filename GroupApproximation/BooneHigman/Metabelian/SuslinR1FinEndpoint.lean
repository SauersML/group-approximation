import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinCoord
import GroupApproximation.BooneHigman.Metabelian.SuslinR1Finite
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatching
import GroupApproximation.Meta.AxiomGuard

/-!
# R1, finite form: the endpoint

Lane `bh-met-90r`.  Target: `SuslinR1FiniteStatement`.

* Char `p` half: PROVED from R2 (`SuslinHorrocksR2Statement`), via Nagata's change of variables
  over the field `ZMod p` (`suslinR1Fin_coord_of_field`) and `suslinR1Fin_normalized_of_coord`.
* `ℤ[1/m]` half: reduced to `SuslinR1FinIntCoordStatement`, the coordinate-change ("monic
  trick") Statement for the `ℤ[1/m][s_1,…,s_k]` family.

**LOUD: strength of `SuslinR1FinIntCoordStatement`.**  It is TRUE: it follows from
`SuslinLocalHorrocksStatement` (true by Suslin), formalized as
`suslinR1Fin_intCoord_of_localHorrocks` (take `φ = id`, `ε = τ⁻¹`).  It is NOT logically strictly
weaker than the `ℤ` half of the target: given R2 the two are EQUIVALENT
(`IntCoord + R2 → R1Finite → LocalHorrocks → IntCoord`, all formalized here).  It is strictly
SMALLER IN PROOF CONTENT: only the `ℤ` family remains (the char `p` half is discharged), and it is
a global statement about `A[X]` with no localization, no finiteness and no Horrocks step; the
local step, the finiteness and the local-global patching are proved in
`SuslinR1FinLocal.lean` / `SuslinR1FinCoord.lean`.

**Why the `ℤ` half is not closed.**  Over `ℤ[1/m][s]`, Nagata's automorphism makes the leading
coefficient a nonzero element of `ℤ[1/m]`, which is not a unit in general; Suslin's argument
there needs an additional elementary factor `ε` (the `ε` in the Statement).

**The criterion "monic modulo 𝔪" is FALSE** as a finiteness criterion: `1 + yX` over `k[y]_(y)`
(see `SuslinR1FinCoord.lean`).  That is why a unit leading coefficient is required.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The `ℤ[1/m]` coordinate-change Statement** (the remaining gap): `SuslinR1FinCoordLocal`
for the family `ℤ[1/m][s_1,…,s_k]`, under the hypotheses of `SuslinR1FiniteStatement`. -/
def SuslinR1FinIntCoordStatement : Prop :=
  ∀ (m k N : ℕ),
    (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
      SuslinR1FinCoordLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1FinIntCoordStatement

/-- **The char `p` family, from R2**: normalized matrices over `𝔽_p[s_1,…,s_k][X]` are
elementary. -/
theorem suslinR1Fin_charP_normalized (h2 : SuslinHorrocksR2Statement) (p : ℕ) [Fact p.Prime]
    (k N : ℕ) (hk : 1 ≤ k)
    (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N')
    (hN : 3 ≤ N) : SuslinMonicNormalizedElementary (Chain.CharPPoly p k) N :=
  suslinR1Fin_normalized_of_coord hN (hA N hN) (h2.1 p k N hk hA hN)
    (suslinR1Fin_coord_of_field (K := ZMod p) (n := k) (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_charP_normalized

/-- **The target, from the `ℤ` coordinate Statement and R2.** -/
theorem suslinR1Fin_finite_of_intCoord (hc : SuslinR1FinIntCoordStatement)
    (h2 : SuslinHorrocksR2Statement) : SuslinR1FiniteStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR1Fin_finiteLocal_of_normalized hN
      (suslinR1Fin_charP_normalized h2 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR1Fin_finiteLocal_of_normalized hN
      (suslinR1Fin_normalized_of_coord hN (hA N hN) (h2.2 m k N hA hN) (hc m k N hA hN))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_finite_of_intCoord

/-- **Local Horrocks, from the `ℤ` coordinate Statement and R2.** -/
theorem suslinR1Fin_localHorrocks_of_intCoord (hc : SuslinR1FinIntCoordStatement)
    (h2 : SuslinHorrocksR2Statement) : SuslinLocalHorrocksStatement :=
  suslinR1_localHorrocks_of_fin (suslinR1Fin_finite_of_intCoord hc h2) h2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_localHorrocks_of_intCoord

/-- **Truth of the gap**: local Horrocks (true by Suslin) implies the `ℤ` coordinate
Statement. -/
theorem suslinR1Fin_intCoord_of_localHorrocks (h : SuslinLocalHorrocksStatement) :
    SuslinR1FinIntCoordStatement := fun m k N hA hN ↦
  suslinR1Fin_coord_of_normalized (by omega) ((suslinPatching_of_localHorrocks h).2 m k N hA hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_intCoord_of_localHorrocks

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
