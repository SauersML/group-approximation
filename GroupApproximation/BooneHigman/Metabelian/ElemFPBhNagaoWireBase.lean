import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SplitStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2RingEquiv
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilGeneric
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJRedMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao's theorem, transported to the rings of the leaf `P1`

Lane `bh-met-94c`, part 1 of 3.  Nagao's theorem in the repo is
`k2PolyNagaoJRed_K2_bot_of_statement`: `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.  It is conditional on
the residual `k2PolyNagaoJRed_Statement` of lane 94a and on the torus interface
`k2PolyNagaoJRed_TorusIface` of lane 94b.  No `ElemFPK2PolyNagaoTorus*` module exists yet, so
both stay hypotheses here.

The leaf `P1 = PolyK2NilGapStatementOver (ZMod p) 4` names `F_p[X]` in two other forms:
* `Polynomial (MvPolynomial (Fin 0) (ZMod p))`, the ring of the `k = 0` instance of
  `PolyK2OneVarNilStatementOver`;
* `MvPolynomial (Fin 1) (ZMod p)`, the ring of the `k = 1` instance of
  `PolyK2StabRangeDiagStatementOver`.
The identification `R[s_0] ≅ R[∅][s_0] ≅ R[X]` is `MvPolynomial.finSuccEquiv` at `n = 0`,
followed by `Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv ..)`.

* `bhNagaoWire_K2_bot_of_ringEquiv` (imported from `ElemFPK2RingEquiv`): `K₂(I, -) = ⊥` is
  invariant under ring isomorphisms.
* `bhNagaoWire_K2_bot_mvFinOne`, `bhNagaoWire_K2_bot_polyFinZero`: the two transports.
* `bhNagaoWire_oneVarNilOver_zero`: the `k = 0` instance of `PolyK2OneVarNilStatementOver`.
  LOUD: `ElemFPBhNagaoWireZeroOne` shows that this instance follows from the `k = 1` instance.
  So Nagao does not shrink the OneVarNil conjunct of `P1`; its genuine use in `P1` is the base
  instance of the StabRangeDiag conjunct (`ElemFPBhNagaoWireDiag`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `F_p[s_0] ≅ F_p[X]`: Nagao's vanishing for `MvPolynomial (Fin 1) (ZMod p)`. -/
theorem bhNagaoWire_K2_bot_mvFinOne {p N : ℕ} (h : K2n N (Polynomial (ZMod p)) = ⊥) :
    K2n N (MvPolynomial (Fin 1) (ZMod p)) = ⊥ :=
  bhNagaoWire_K2_bot_of_ringEquiv
    ((MvPolynomial.finSuccEquiv (ZMod p) 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)))) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_K2_bot_mvFinOne

/-- `F_p[∅][X] ≅ F_p[X]`: Nagao's vanishing for `Polynomial (MvPolynomial (Fin 0) (ZMod p))`. -/
theorem bhNagaoWire_K2_bot_polyFinZero {p N : ℕ} (h : K2n N (Polynomial (ZMod p)) = ⊥) :
    K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p))) = ⊥ :=
  bhNagaoWire_K2_bot_of_ringEquiv
    (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0))) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_K2_bot_polyFinZero

/-- Nagao's theorem in the repo (conditional on lanes 94a and 94b), at every rank `N ≥ 5`. -/
theorem bhNagaoWire_K2_bot_nagao (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) {p : ℕ} (hp : p.Prime) :
    ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥ :=
  fun _ hN ↦ k2PolyNagaoJRed_K2_bot_of_statement hR hT hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_K2_bot_nagao

/-- **The `k = 0` instance of `PolyK2OneVarNilStatementOver (ZMod p)`** from `K₂(N, F_p[X]) = ⊥`
for `N ≥ 5`.  The hypothesis `ev₀ u = 1` is not even needed.  LOUD: this instance is implied
by the `k = 1` instance (`bhNagaoWire_oneVarNilZero_of_one`). -/
theorem bhNagaoWire_oneVarNilOver_zero {p : ℕ}
    (hK2 : ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥) (N : ℕ) (hN : 0 + 5 ≤ N)
    (u : K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p)))) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) (ZMod p))) (Fin.castLEEmb hNM) u = 1 :=
  ⟨N, le_rfl, by
    rw [eq_one_of_K2_eq_bot (bhNagaoWire_K2_bot_polyFinZero (hK2 N (by omega))) u, map_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_oneVarNilOver_zero

/-- The `k = 0` instance of `PolyK2OneVarNilStatementOver (ZMod p)`, from Nagao's theorem
(conditional on lanes 94a and 94b). -/
theorem bhNagaoWire_oneVarNilOver_zero_of_nagao (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) {p : ℕ} (hp : p.Prime) (N : ℕ) (hN : 0 + 5 ≤ N)
    (u : K2n N (Polynomial (MvPolynomial (Fin 0) (ZMod p)))) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) (ZMod p))) (Fin.castLEEmb hNM) u = 1 :=
  bhNagaoWire_oneVarNilOver_zero (bhNagaoWire_K2_bot_nagao hR hT hp) N hN u

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_oneVarNilOver_zero_of_nagao

end GroupApproximation.BooneHigman.Metabelian.ElemFP
