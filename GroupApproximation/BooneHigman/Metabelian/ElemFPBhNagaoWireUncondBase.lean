import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusWireJRed
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusWireLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao wiring endpoints with both residuals discharged

Lane `bh-wire-01`, part 1 of 3 (a wiring lane: no new residual).  The lane-94a residual
`k2PolyNagaoJRed_Statement` is proved (`k2PolyNagaoJRes_statement`, per prime
`k2PolyNagaoJRes_resAt p`), and so is the lane-94b torus interface `k2PolyNagaoJRed_TorusIface`
(`k2PolyNagaoTorus_torusIface`, per prime `k2PolyNagaoTorus_torusAt p`).  Every endpoint of
`ElemFPBhNagaoWireBase`, `ElemFPBhNagaoWireDiag`, `ElemFPK2PolyNagaoTorusWireJRed` and
`ElemFPK2PolyNagaoTorusWireLeaf` that took `hR` and/or `hT` gets an `_uncond` version here.  All
other hypotheses are kept exactly.  (`ElemFPBhNagaoWireZeroOne` has no such endpoint.)

LOUD: the `SpecPos` hypothesis `bhNagaoWire_SpecPosStatementOver` and the OneVarNil hypothesis
remain on the `nilGapOver` / `polynomialFpK2Vanishing` endpoints.  Nagao discharges only the
one-variable base instance of the StabRangeDiag conjunct of `P1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

/-! ### `ElemFPBhNagaoWireBase` / `ElemFPBhNagaoWireDiag` (both `hR` and `hT` removed) -/

/-- Unconditional `bhNagaoWire_K2_bot_nagao`: `K₂(N, F_p[X]) = ⊥` for every `N ≥ 5`. -/
theorem bhNagaoUncond_wire_K2_bot_nagao {p : ℕ} (hp : p.Prime) :
    ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥ :=
  bhNagaoWire_K2_bot_nagao k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface hp

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_wire_K2_bot_nagao

/-- Unconditional `bhNagaoWire_oneVarNilOver_zero_of_nagao`: the `k = 0` instance of
`PolyK2OneVarNilStatementOver (ZMod p)`. -/
theorem bhNagaoUncond_wire_oneVarNilOver_zero_of_nagao {p : ℕ} (hp : p.Prime) (N : ℕ)
    (hN : 0 + 5 ≤ N) (u : K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p)))) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) (ZMod p))) (Fin.castLEEmb hNM) u = 1 :=
  bhNagaoWire_oneVarNilOver_zero_of_nagao k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface
    hp N hN u

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_wire_oneVarNilOver_zero_of_nagao

/-- `bhNagaoWire_nilGapOver_of_specPos` without `hR`, `hT`: OneVarNil and `SpecPos` at `p`
give `P1` at `p`. -/
theorem bhNagaoUncond_wire_nilGapOver_of_specPos {p : ℕ} (hp : p.Prime)
    (hone : PolyK2OneVarNilStatementOver (ZMod p))
    (hpos : bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  bhNagaoWire_nilGapOver_of_specPos hp k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface
    hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_wire_nilGapOver_of_specPos

/-- `bhNagaoWire_polynomialFpK2Vanishing` without `hR`, `hT`. -/
theorem bhNagaoUncond_wire_polynomialFpK2Vanishing (hone : PolyK2OneVarNilStatement)
    (hpos : ∀ p : ℕ, p.Prime → bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolynomialFpK2VanishingStatement :=
  bhNagaoWire_polynomialFpK2Vanishing k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface
    hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_wire_polynomialFpK2Vanishing

/-! ### `ElemFPK2PolyNagaoTorusWireJRed` (`hR` removed) -/

/-- Unconditional `k2PolyNagaoTorusWire_check_of_resAt` (`hR := k2PolyNagaoJRes_resAt p`). -/
theorem bhNagaoUncond_torusWire_check_of_resAt {p : ℕ} [Fact p.Prime]
    {I : Type} [Fintype I] [DecidableEq I] (K : Finset I)
    (m L : I) (hmL : m ≠ L) (hLK : L ∉ K) (hmK : m ∈ K) (him : ∃ i ∈ K, i ≠ m)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hSK : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    (hJ : k2PolyNagaoWide_Stab p (K.erase m) m) :
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p))) :=
  k2PolyNagaoTorusWire_check_of_resAt (k2PolyNagaoJRes_resAt p) K m L hmL hLK hmK him hthird
    hconst hSK hJ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_check_of_resAt

/-- Unconditional `k2PolyNagaoTorusWire_wide_of_statement`. -/
theorem bhNagaoUncond_torusWire_wide_of_statement : k2PolyNagaoWide_Statement :=
  k2PolyNagaoTorusWire_wide_of_statement k2PolyNagaoJRes_statement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_wide_of_statement

/-- Unconditional `k2PolyNagaoTorusWire_root_of_statement`. -/
theorem bhNagaoUncond_torusWire_root_of_statement : k2PolyNagaoRoot_Statement :=
  k2PolyNagaoTorusWire_root_of_statement k2PolyNagaoJRes_statement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_root_of_statement

/-- Unconditional `k2PolyNagaoTorusWire_K2_bot_of_statement`. -/
theorem bhNagaoUncond_torusWire_K2_bot_of_statement {p : ℕ} (hp : p.Prime) {N : ℕ}
    (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoTorusWire_K2_bot_of_statement k2PolyNagaoJRes_statement hp hN

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_K2_bot_of_statement

/-! ### `ElemFPK2PolyNagaoTorusWireLeaf` (`hR` removed) -/

/-- Unconditional `k2PolyNagaoTorusWire_K2_bot_nagao`. -/
theorem bhNagaoUncond_torusWire_K2_bot_nagao {p : ℕ} (hp : p.Prime) :
    ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoTorusWire_K2_bot_nagao k2PolyNagaoJRes_statement hp

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_K2_bot_nagao

/-- Unconditional `k2PolyNagaoTorusWire_oneVarNilOver_zero_of_nagao`. -/
theorem bhNagaoUncond_torusWire_oneVarNilZero {p : ℕ} (hp : p.Prime) (N : ℕ)
    (hN : 0 + 5 ≤ N) (u : K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p)))) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) (ZMod p))) (Fin.castLEEmb hNM) u = 1 :=
  k2PolyNagaoTorusWire_oneVarNilOver_zero_of_nagao k2PolyNagaoJRes_statement hp N hN u

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_oneVarNilZero

/-- Unconditional `k2PolyNagaoTorusWire_base_of_statement`: the one-variable base instance of
the StabRangeDiag conjunct of `P1` (over `F_p[s]`, ranks `N ≥ 1 + 4`). -/
theorem bhNagaoUncond_torusWire_base_of_statement {p : ℕ} (hp : p.Prime) :
    ∀ N : ℕ, 1 + 4 ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) (ZMod p)) u = 1 → u = 1 :=
  k2PolyNagaoTorusWire_base_of_statement k2PolyNagaoJRes_statement hp

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_base_of_statement

/-- `k2PolyNagaoTorusWire_nilGapOver_of_specPos` without `hR`. -/
theorem bhNagaoUncond_torusWire_nilGapOver_of_specPos {p : ℕ} (hp : p.Prime)
    (hone : PolyK2OneVarNilStatementOver (ZMod p))
    (hpos : bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  k2PolyNagaoTorusWire_nilGapOver_of_specPos hp k2PolyNagaoJRes_statement hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_nilGapOver_of_specPos

/-- `k2PolyNagaoTorusWire_polynomialFpK2Vanishing` without `hR`. -/
theorem bhNagaoUncond_torusWire_polynomialFpK2Vanishing (hone : PolyK2OneVarNilStatement)
    (hpos : ∀ p : ℕ, p.Prime → bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolynomialFpK2VanishingStatement :=
  k2PolyNagaoTorusWire_polynomialFpK2Vanishing k2PolyNagaoJRes_statement hone hpos

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_torusWire_polynomialFpK2Vanishing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
