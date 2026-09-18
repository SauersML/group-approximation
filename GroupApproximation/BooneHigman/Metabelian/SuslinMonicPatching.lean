import GroupApproximation.BooneHigman.Metabelian.SuslinMonicKaroubi
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin monic route, part 3: reduction of the one-variable step to the normalized case

Lane `bh-met-41`.  `SuslinOneVariableStatement` (`AbsorptionSuslinReduction.lean`) asks, for
`A = F_p[s_0, ..., s_{k-1}]` (`k ≥ 1`) and `A = ℤ[1/m][t_0, ..., t_{k-1}]`, given
`SL_{N'}(A) = E_{N'}(A)` for all `N' ≥ 3`, that `SL_N(A[X]) = E_N(A[X])` for `N ≥ 3`.

No patching interface (`SuslinPatch*`, lane `bh-met-40`) exists in the repository, so the
interface is stated here as one Statement, `SuslinPatchingStatement`: under the same
hypotheses, every **normalized** `τ ∈ SL_N(A[X])` (`τ(0) = 1`) is elementary.  This is exactly
the output of the local-global route: Suslin's local-global principle (a normalized `τ` that is
elementary over `A_𝔪[X]` for every maximal ideal `𝔪` is elementary over `A[X]`) combined with the
local step over `A_𝔪[X]` (Horrocks: Euclidean reduction on a monic entry, whose division half is
`suslinMonic_exists_row_degree_lt`, after the change of variables `X_i ↦ X_i + X^M` producing a
monic entry).

`suslinOneVariable_of_patching` proves the one-variable step from it by Karoubi's normalization
`σ(X) σ(0)⁻¹` (`suslinMonic_specialLinearInElementary_polynomial_of_normalized`), using the
hypothesis `SL_N(A) = E_N(A)` for the constant part.

**Why the isolated statement is strictly smaller and true.**  It has the same hypotheses as
`SuslinOneVariableStatement` and only asks the conclusion for the matrices with `τ(0) = 1`;
the passage from an arbitrary `σ` (evaluation at `0`, the constant part being elementary by
hypothesis, determinant bookkeeping) is proved here.  It is true, since every conclusion of it
is a special case of the corresponding conclusion of `SuslinOneVariableStatement`, which holds
by Suslin's theorem (A. A. Suslin, *On the structure of the special linear group over polynomial
rings*, 1977; see the docstring of `AbsorptionSuslinReduction.lean`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The normalized one-variable Suslin step** (patching interface): for the two coefficient
families, given `SL_{N'} = E_{N'}` over `A` for all `N' ≥ 3`, every `τ ∈ SL_N(A[X])` with
`τ(0) = 1` is elementary for `N ≥ 3`. -/
def SuslinPatchingStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinMonicNormalizedElementary (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinMonicNormalizedElementary (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinPatchingStatement

/-- **The reduction**: the normalized step gives the one-variable Suslin step. -/
theorem suslinOneVariable_of_patching (h : SuslinPatchingStatement) :
    SuslinOneVariableStatement :=
  ⟨fun p _ k N hk hA hN ↦
      suslinMonic_specialLinearInElementary_polynomial_of_normalized (hA N hN)
        (h.1 p k N hk hA hN),
    fun m k N hA hN ↦
      suslinMonic_specialLinearInElementary_polynomial_of_normalized (hA N hN)
        (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinOneVariable_of_patching

/-- Both chain absorption leaves from the normalized one-variable Suslin step. -/
theorem elementaryAbsorptionStatements_of_patching (h : SuslinPatchingStatement) :
    Chain.CharPElementaryAbsorptionStatement ∧ Chain.CharZeroElementaryAbsorptionStatement :=
  elementaryAbsorptionStatements_of_oneVariable (suslinOneVariable_of_patching h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.elementaryAbsorptionStatements_of_patching

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
