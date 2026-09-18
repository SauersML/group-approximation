import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilTelescope
import GroupApproximation.Meta.AxiomGuard

/-!
# The generic nil statements specialize to the char-`p` statements

Lane `bh-met-37`, specialization module.  The ring-generic statements of
`ElemFPCharZeroK2NilGeneric` at the base ring `A = ZMod p` are, by definition, the char-`p`
statements of lanes `bh-met-14`, `bh-met-22` and `bh-met-29`:

* `polyK2OneVarNil_iff_forall_over`: `PolyK2OneVarNilStatement ↔ ∀ p prime,
  PolyK2OneVarNilStatementOver (ZMod p)`;
* `polyK2Nil_iff_forall_over`: `PolyK2NilStatement ↔ ∀ p prime, PolyK2NilStatementOver (ZMod p)`;
* `polyK2StabRangeDiag_iff_forall_over`: `PolyK2StabRangeDiagStatement ↔ ∀ p prime,
  PolyK2StabRangeDiagStatementOver (ZMod p) 4`;
* `polyK2NilStabilityPos_iff_forall_over`: `PolyK2NilStabilityPosStatement ↔ ∀ p prime,
  PolyK2NilStabilityStatementOver (ZMod p) 4` (the char-`p` statement carries a redundant
  hypothesis `N ≥ 5`, implied by `k ≥ 1` and `N ≥ k + 4`).

So both chains share one statement form.  `polynomialFpK2Vanishing_of_gapOver` is the char-`p`
combined endpoint with the gap pair `PolyK2NilGapStatementOver (ZMod p) 4` in place of the two
char-`p` gaps.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- The char-`p` one-variable nil statement is the generic one over every `ZMod p`, `p` prime. -/
theorem polyK2OneVarNil_iff_forall_over :
    PolyK2OneVarNilStatement ↔ ∀ p : ℕ, p.Prime → PolyK2OneVarNilStatementOver (ZMod p) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_iff_forall_over

/-- The char-`p` nil statement is the generic one over every `ZMod p`, `p` prime. -/
theorem polyK2Nil_iff_forall_over :
    PolyK2NilStatement ↔ ∀ p : ℕ, p.Prime → PolyK2NilStatementOver (ZMod p) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2Nil_iff_forall_over

/-- The char-`p` diagonal stability statement is the generic one at offset `4` over every
`ZMod p`, `p` prime. -/
theorem polyK2StabRangeDiag_iff_forall_over :
    PolyK2StabRangeDiagStatement ↔
      ∀ p : ℕ, p.Prime → PolyK2StabRangeDiagStatementOver (ZMod p) 4 :=
  Iff.rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiag_iff_forall_over

/-- The char-`p` stability statement on `ker ev₀` is the generic one at offset `4` over every
`ZMod p`, `p` prime. -/
theorem polyK2NilStabilityPos_iff_forall_over :
    PolyK2NilStabilityPosStatement ↔
      ∀ p : ℕ, p.Prime → PolyK2NilStabilityStatementOver (ZMod p) 4 :=
  ⟨fun h p hp k N hk hkN u hu0 hu ↦ h p hp k N hk hkN (by omega) u hu0 hu,
    fun h p hp k N hk hkN _ u hu0 hu ↦ h p hp k N hk hkN u hu0 hu⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilStabilityPos_iff_forall_over

/-- **Char-`p` combined endpoint with the generic gap pair**: the gap pair over every `ZMod p` and
the field case give `K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_gapOver
    (hgap : ∀ p : ℕ, p.Prime → PolyK2NilGapStatementOver (ZMod p) 4)
    (hfield : FieldK2VanishingStatement) : PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_stabRangeDiag
    (polyK2StabRangeDiag_iff_forall_over.mpr fun p hp ↦ (hgap p hp).2)
    (polyK2NilPos_of_oneVar (polyK2OneVarNil_iff_forall_over.mpr fun p hp ↦ (hgap p hp).1))
    hfield

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_gapOver

end GroupApproximation.BooneHigman.Metabelian.ElemFP
