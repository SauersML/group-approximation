import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireDiag
import GroupApproximation.Meta.AxiomGuard

/-!
# The Nagao torus wired into the leaf `P1` endpoints

Lane `bh-met-94d`, part 2 of 2 (a wiring lane: no new residual).  The endpoints of
`ElemFPBhNagaoWireBase` and `ElemFPBhNagaoWireDiag` (lane 94c) took the torus interface
`hT : k2PolyNagaoJRed_TorusIface` as a hypothesis.  It is now proved
(`k2PolyNagaoTorus_torusIface`, lane 94b), so every such endpoint loses `hT`:

* `k2PolyNagaoTorusWire_K2_bot_nagao` (from `bhNagaoWire_K2_bot_nagao`);
* `k2PolyNagaoTorusWire_oneVarNilOver_zero_of_nagao` (from
  `bhNagaoWire_oneVarNilOver_zero_of_nagao`);
* `k2PolyNagaoTorusWire_base_of_statement`: the base instance of the StabRangeDiag conjunct
  (`bhNagaoWire_base_of_K2_bot` at `d = 4`);
* `k2PolyNagaoTorusWire_nilGapOver_of_specPos` (from `bhNagaoWire_nilGapOver_of_specPos`);
* `k2PolyNagaoTorusWire_polynomialFpK2Vanishing` (from `bhNagaoWire_polynomialFpK2Vanishing`).

The remaining hypotheses are unchanged: the lane-94a residual `k2PolyNagaoJRed_Statement`, the
OneVarNil conjunct, and the lane-94c residual `bhNagaoWire_SpecPosStatementOver`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- Nagao's theorem in the repo, torus discharged: the lane-94a residual alone gives
`K₂(N, F_p[X]) = ⊥` at every rank `N ≥ 5`. -/
theorem k2PolyNagaoTorusWire_K2_bot_nagao (hR : k2PolyNagaoJRed_Statement) {p : ℕ}
    (hp : p.Prime) : ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥ :=
  bhNagaoWire_K2_bot_nagao hR k2PolyNagaoTorus_torusIface hp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_K2_bot_nagao

/-- The `k = 0` instance of `PolyK2OneVarNilStatementOver (ZMod p)`, from the lane-94a residual
alone. -/
theorem k2PolyNagaoTorusWire_oneVarNilOver_zero_of_nagao (hR : k2PolyNagaoJRed_Statement)
    {p : ℕ} (hp : p.Prime) (N : ℕ) (hN : 0 + 5 ≤ N)
    (u : K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p)))) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) (ZMod p))) (Fin.castLEEmb hNM) u = 1 :=
  bhNagaoWire_oneVarNilOver_zero_of_nagao hR k2PolyNagaoTorus_torusIface hp N hN u

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_oneVarNilOver_zero_of_nagao

/-- The one-variable base instance of the StabRangeDiag conjunct of `P1` (over `F_p[s]`, ranks
`N ≥ 1 + 4`), from the lane-94a residual alone. -/
theorem k2PolyNagaoTorusWire_base_of_statement (hR : k2PolyNagaoJRed_Statement) {p : ℕ}
    (hp : p.Prime) :
    ∀ N : ℕ, 1 + 4 ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) (ZMod p)) u = 1 → u = 1 :=
  bhNagaoWire_base_of_K2_bot le_rfl (k2PolyNagaoTorusWire_K2_bot_nagao hR hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_base_of_statement

/-- **Endpoint at `P1`, torus discharged**: the lane-94a residual, the OneVarNil conjunct and the
lane-94c residual give `P1 = PolyK2NilGapStatementOver (ZMod p) 4`. -/
theorem k2PolyNagaoTorusWire_nilGapOver_of_specPos {p : ℕ} (hp : p.Prime)
    (hR : k2PolyNagaoJRed_Statement) (hone : PolyK2OneVarNilStatementOver (ZMod p))
    (hpos : bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  bhNagaoWire_nilGapOver_of_specPos hp hR k2PolyNagaoTorus_torusIface hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_nilGapOver_of_specPos

/-- **Global endpoint, torus discharged**: `PolynomialFpK2VanishingStatement` from the lane-94a
residual, the OneVarNil statement, and the lane-94c residual at every prime. -/
theorem k2PolyNagaoTorusWire_polynomialFpK2Vanishing (hR : k2PolyNagaoJRed_Statement)
    (hone : PolyK2OneVarNilStatement)
    (hpos : ∀ p : ℕ, p.Prime → bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolynomialFpK2VanishingStatement :=
  bhNagaoWire_polynomialFpK2Vanishing hR k2PolyNagaoTorus_torusIface hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_polynomialFpK2Vanishing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
