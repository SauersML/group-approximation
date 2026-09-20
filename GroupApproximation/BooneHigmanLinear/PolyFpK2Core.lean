import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilCharP
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarNilCube
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# Polynomial `K₂` statements and generic stability reductions

These definitions and reductions are independent of the Boone–Higman host and envelope
constructions. `PolyFpK2` imports this foundation and assembles the group-theoretic endpoints;
the `K2Poly` development imports it directly.
-/

namespace GroupApproximation
namespace BooneHigmanLinear

open GroupApproximation.BooneHigman

/-- **The owed char-`p` input.** `K₂(N, F_p[s₁..s_k]) = ⊥` for `p` prime, `k ≥ 2` and
`N ≥ k + 4`. -/
def PolyFpK2VanishingGeTwoStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 2 ≤ k → k + 4 ≤ N →
    SteinbergBasic.K2 (Fin N) (MvPolynomial (Fin k) (ZMod p)) = ⊥

#audit_axioms GroupApproximation.BooneHigmanLinear.PolyFpK2VanishingGeTwoStatement

/-- The owed statement is no stronger than `P1`. -/
theorem polyFpK2VanishingGeTwo_of_gapOver
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4) :
    PolyFpK2VanishingGeTwoStatement := fun p hp k N hk hkN =>
  Metabelian.ElemFP.polynomialFpK2Vanishing_of_gapOver hP1
    Metabelian.ElemFP.vdkRowExt_fieldK2Vanishing p hp k N hkN (by omega)

#audit_axioms GroupApproximation.BooneHigmanLinear.polyFpK2VanishingGeTwo_of_gapOver

/-- `K₂(N, F_p[s₁..s_k]) = ⊥` for every `k` and every `N ≥ 5`: Tulenbaev's injective stability
(`TulenbaevInjStabFpStatement`) plus stable vanishing (`StableK2PolyFpVanishingStatement`). -/
def TulenbaevPolyFpK2Statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 5 ≤ N →
    SteinbergBasic.K2 (Fin N) (MvPolynomial (Fin k) (ZMod p)) = ⊥

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevPolyFpK2Statement

/-- Tulenbaev's theorem gives the owed statement. -/
theorem polyFpK2VanishingGeTwo_of_tulenbaev (h : TulenbaevPolyFpK2Statement) :
    PolyFpK2VanishingGeTwoStatement := fun p hp k N hk hkN => h p hp k N (by omega)

#audit_axioms GroupApproximation.BooneHigmanLinear.polyFpK2VanishingGeTwo_of_tulenbaev

/-- **Tulenbaev's injective stability over `F_p`** (Theorem 5.3 of *The Steinberg group of a
polynomial ring*, for `A = F_p`): for `N ≥ 5` and every `k`, an element of `K₂(N, F_p[s₁..s_k])`
that dies after padding is trivial. -/
def TulenbaevInjStabFpStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 5 ≤ N →
    ∀ u : SteinbergBasic.K2 (Fin N) (MvPolynomial (Fin k) (ZMod p)),
      Metabelian.ElemFP.K2DiesAfterPadding u → u = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevInjStabFpStatement

/-- **Stable `K₂(F_p[s₁..s_k]) = 0`**: every element of `K₂(N, F_p[s₁..s_k])` dies after padding. -/
def StableK2PolyFpVanishingStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ,
    ∀ u : SteinbergBasic.K2 (Fin N) (MvPolynomial (Fin k) (ZMod p)),
      Metabelian.ElemFP.K2DiesAfterPadding u

#audit_axioms GroupApproximation.BooneHigmanLinear.StableK2PolyFpVanishingStatement

/-- Injective stability and stable vanishing give `K₂(N, F_p[s₁..s_k]) = ⊥` for `N ≥ 5`. -/
theorem tulenbaevPolyFpK2_of_injStab_of_stable (hinj : TulenbaevInjStabFpStatement)
    (hst : StableK2PolyFpVanishingStatement) : TulenbaevPolyFpK2Statement := by
  intro p hp k N hN
  refine eq_bot_iff.mpr fun g hg => ?_
  have h1 := hinj p hp k N hN ⟨g, hg⟩ (hst p hp k N ⟨g, hg⟩)
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)

#audit_axioms GroupApproximation.BooneHigmanLinear.tulenbaevPolyFpK2_of_injStab_of_stable

end BooneHigmanLinear
end GroupApproximation
