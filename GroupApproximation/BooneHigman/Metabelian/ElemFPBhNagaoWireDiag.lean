import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireBase
import GroupApproximation.BooneHigman.Metabelian.ElemFPStabDiagFpSpec
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao's theorem wired into the leaf `P1 = PolyK2NilGapStatementOver (ZMod p) 4`

Lane `bh-met-94c`, part 3 of 3.  Write `R_k = F_p[s_1..s_k]` and `cc : R_k → F_p`.

## Where Nagao enters `P1`

`P1` has two conjuncts.
* OneVarNil (`PolyK2OneVarNilStatementOver (ZMod p)`).  Nagao covers only its `k = 0` instance,
  and that instance follows from the `k = 1` instance (`ElemFPBhNagaoWireZeroOne`, LOUD).  So
  OneVarNil is passed through **unchanged** as a hypothesis.  Its instances `k ≥ 1` are
  `NK₂`-vanishing statements for `F_p[s_1..s_k]` (Quillen), beyond Nagao.
* StabRangeDiag.  Lane 95a reduced it, by induction on the number of variables, to the residual
  `stabDiagFp_SpecStatementOver (ZMod p) 4` (instances `k ≥ 0`, ring `R_{k+1}`).  Its base
  instance `k = 0` is over `R_1 = F_p[s]`, and `K₂(N, F_p[s]) = ⊥` for `N ≥ 5` (Nagao, through
  `finSuccEquiv` at `n = 0`) kills it outright.

## The new residual

`bhNagaoWire_SpecPosStatementOver A d`: the instances `k ≥ 1` of `stabDiagFp_SpecStatementOver`,
reindexed as `k + 1`.  Honest strength:
* **Weaker**: it is a restriction of the lane-95a residual (`bhNagaoWire_specPos_of_spec`).
* **Strictly smaller in proof content**: the one-variable base instance is discharged by Nagao
  (`bhNagaoWire_base_of_K2_bot`), with Nagao's own inputs (lanes 94a, 94b) as hypotheses.
  Conversely, `SpecPos` plus the base gives the lane-95a residual
  (`bhNagaoWire_spec_of_specPos`).  No derivation of the base from `SpecPos` alone is known.
  (The retract argument of `ElemFPBhNagaoWireZeroOne` does not transfer here: that argument
  needs a conclusion insensitive to one more padding step, and `SpecPos` only speaks about
  `K2Stab` at one rank.)
* Not claimed: that `SpecPos` is logically strictly weaker than the lane-95a residual.  Both
  are true, so this cannot be shown by a counterexample.

## Truth check

`SpecPos (ZMod p) 4` follows from `stabDiagFp_SpecStatementOver (ZMod p) 4`, which is equivalent
to `PolyK2StabRangeDiagStatementOver (ZMod p) 4` (`stabDiagFp_spec_iff_stabRangeDiagOver`).
That is true: `sr(F_p[s_1..s_k]) ≤ k + 1` (Bass), and van der Kallen's injective stability for
`K₂` holds at ranks `n ≥ sr + 2`.  The instances of `SpecPos` have `k + 2` variables and rank
`N ≥ k + 6`, which is enough.  The base instance uses ranks `N ≥ 1 + 4 = 5`, exactly Nagao's
range.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The residual of lane `bh-met-94c`**: `stabDiagFp_SpecStatementOver A d` at `k + 1`, i.e. for
`R_{k+2} = A[s_0..s_{k+1}]` and every rank `N ≥ (k + 2) + d`, an element of `K₂(N, R_{k+2})`
with `K2Stab N u = 1` that is killed by every augmented specialization `R_{k+2} → R_{k+1}` is
trivial.  TRUE (module docstring).  It is a restriction of the lane-95a residual.  It is
strictly smaller in proof content, because the base instance over `A[s]` is Nagao's theorem
(`bhNagaoWire_base_of_K2_bot`). -/
def bhNagaoWire_SpecPosStatementOver (A : Type*) [CommRing A] (d : ℕ) : Prop :=
  ∀ k N : ℕ, k + 1 + 1 + d ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1 + 1)) A),
      (∀ φ : MvPolynomial (Fin (k + 1 + 1)) A →+* MvPolynomial (Fin (k + 1)) A,
        (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A).comp φ =
            MvPolynomial.constantCoeff →
          K2Map φ u = 1) →
      K2Stab N (MvPolynomial (Fin (k + 1 + 1)) A) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_SpecPosStatementOver

/-- The lane-95a residual gives the new residual (restriction to `k + 1`). -/
theorem bhNagaoWire_specPos_of_spec (A : Type*) [CommRing A] (d : ℕ)
    (h : stabDiagFp_SpecStatementOver A d) : bhNagaoWire_SpecPosStatementOver A d :=
  fun k N hN u hφ hu ↦ h (k + 1) N hN u hφ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_specPos_of_spec

/-- **Induction on the number of variables, from the one-variable base.**  The base instance
over `A[s]` and the new residual give injective stability on `ker cc` over `A[s_0..s_j]` at every
rank `N ≥ (j + 1) + d`. -/
theorem bhNagaoWire_stab_of_specPos (A : Type*) [CommRing A] (d : ℕ)
    (hbase : ∀ N : ℕ, 1 + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) A) u = 1 → u = 1)
    (h : bhNagaoWire_SpecPosStatementOver A d) (j : ℕ) :
    ∀ N : ℕ, j + 1 + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin (j + 1)) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin (j + 1)) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin (j + 1)) A) u = 1 → u = 1 := by
  induction j with
  | zero =>
    intro N hN u hu0 hu
    exact hbase N (by omega) u hu0 hu
  | succ j ih =>
    intro N hN u hu0 hu
    refine h j N hN u (fun φ hφ ↦ ?_) hu
    refine ih N (by omega) (K2Map φ u) ?_ (stabDiagFp_K2Stab_K2Map_eq_one φ hu)
    rw [K2Map_K2Map, hφ, hu0]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_stab_of_specPos

/-- The base instance and the new residual give the StabRangeDiag conjunct of `P1`'s shape. -/
theorem bhNagaoWire_stabRangeDiagOver_of_specPos (A : Type*) [CommRing A] (d : ℕ)
    (hbase : ∀ N : ℕ, 1 + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) A) u = 1 → u = 1)
    (h : bhNagaoWire_SpecPosStatementOver A d) : PolyK2StabRangeDiagStatementOver A d := by
  intro k hk u hu0 hu
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact bhNagaoWire_stab_of_specPos A d hbase h j (j + 1 + d) le_rfl u hu0 hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_stabRangeDiagOver_of_specPos

/-- The base instance and the new residual give back the lane-95a residual. -/
theorem bhNagaoWire_spec_of_specPos (A : Type*) [CommRing A] (d : ℕ)
    (hbase : ∀ N : ℕ, 1 + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) A) u = 1 → u = 1)
    (h : bhNagaoWire_SpecPosStatementOver A d) : stabDiagFp_SpecStatementOver A d :=
  stabDiagFp_spec_of_stabRangeDiagOver A d (bhNagaoWire_stabRangeDiagOver_of_specPos A d hbase h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_spec_of_specPos

/-- **The base instance from Nagao's vanishing**: over `F_p[s]` at ranks `N ≥ 1 + d ≥ 5`, every
element of `K₂` is trivial, since `K₂(N, F_p[s]) ≅ K₂(N, F_p[X]) = ⊥`. -/
theorem bhNagaoWire_base_of_K2_bot {p d : ℕ} (hd : 4 ≤ d)
    (hK2 : ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥) :
    ∀ N : ℕ, 1 + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin 1) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab N (MvPolynomial (Fin 1) (ZMod p)) u = 1 → u = 1 :=
  fun N hN u _ _ ↦ eq_one_of_K2_eq_bot (bhNagaoWire_K2_bot_mvFinOne (hK2 N (by omega))) u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_base_of_K2_bot

/-- `P1` from `K₂(N, F_p[X]) = ⊥` (`N ≥ 5`), the OneVarNil conjunct, and the new residual. -/
theorem bhNagaoWire_nilGapOver_of_K2_bot {p : ℕ}
    (hK2 : ∀ N : ℕ, 5 ≤ N → K2n N (Polynomial (ZMod p)) = ⊥)
    (hone : PolyK2OneVarNilStatementOver (ZMod p))
    (hpos : bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  ⟨hone, bhNagaoWire_stabRangeDiagOver_of_specPos (ZMod p) 4
    (bhNagaoWire_base_of_K2_bot le_rfl hK2) hpos⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_nilGapOver_of_K2_bot

/-- **Endpoint at `P1`** (lane `bh-met-94c`).  Nagao's theorem, conditional on the lane-94a
residual `hR` and the lane-94b torus interface `hT`, together with the OneVarNil conjunct (passed
through unchanged, see `ElemFPBhNagaoWireZeroOne`) and the new residual `hpos`, gives
`P1 = PolyK2NilGapStatementOver (ZMod p) 4`. -/
theorem bhNagaoWire_nilGapOver_of_specPos {p : ℕ} (hp : p.Prime)
    (hR : k2PolyNagaoJRed_Statement) (hT : k2PolyNagaoJRed_TorusIface)
    (hone : PolyK2OneVarNilStatementOver (ZMod p))
    (hpos : bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  bhNagaoWire_nilGapOver_of_K2_bot (bhNagaoWire_K2_bot_nagao hR hT hp) hone hpos

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_nilGapOver_of_specPos

/-- **Global endpoint**: `PolynomialFpK2VanishingStatement` from Nagao's inputs `hR`, `hT`, the
OneVarNil statement, and the new residual at every prime.  The field input is the proved
`vdkRowExt_fieldK2Vanishing`. -/
theorem bhNagaoWire_polynomialFpK2Vanishing (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) (hone : PolyK2OneVarNilStatement)
    (hpos : ∀ p : ℕ, p.Prime → bhNagaoWire_SpecPosStatementOver (ZMod p) 4) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_gapOver
    (fun p hp ↦ bhNagaoWire_nilGapOver_of_specPos hp hR hT
      (polyK2OneVarNil_iff_forall_over.mp hone p hp) (hpos p hp))
    vdkRowExt_fieldK2Vanishing

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_polynomialFpK2Vanishing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
