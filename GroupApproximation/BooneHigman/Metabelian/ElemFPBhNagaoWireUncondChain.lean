import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondBase
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoSigmaWiring
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWiring
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyEuclidWiring
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNFStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNFWiring
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyFieldSlice
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.BooneHigman.Metabelian.ElemFPEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The Nagao chain, traced upward unconditionally

Lane `bh-wire-01`, part 2 of 3 (a wiring lane: no new residual).  With the lane-94a residual
proved (`k2PolyNagaoJRes_wide : k2PolyNagaoWide_Statement`) and the Weyl half proved
(`k2PolyNagaoWeyl_weylStatement`), every intermediate statement of the Nagao chain is now a
theorem:

`Sigma_Wide ∧ Sigma_Weyl → Mono → Euclid_Gen → NF_Coset → NF_Stab → field-const (N ≥ 5)`,

and the `n = 0` slice statements `nk2Slice_DiesStatement (ZMod p) 0`,
`nk2Slice_LevelStatement (ZMod p) 0` follow.

The strongest `F_p` polynomial vanishing that is now unconditional is the `k ≤ 1` slice of
`PolynomialFpK2VanishingStatement` (`bhNagaoUncond_polynomialFpK2Vanishing_le_one`): `k = 0` is
the field case `vdkRowExt_fieldK2Vanishing`, and `k = 1` is Nagao via `F_p[s_0] ≅ F_p[X]`.
LOUD: `k ≥ 2` is NOT covered.  It still needs the StabRangeDiag conjunct of `P1` at `k ≥ 2`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- The wide half of the σ-statement, unconditionally. -/
theorem bhNagaoUncond_sigmaWide : k2PolyNagaoSigma_WideStatement :=
  k2PolyNagaoWide_wide_of_statement k2PolyNagaoJRes_wide

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_sigmaWide

/-- The full σ-statement (wide and Weyl halves), unconditionally. -/
theorem bhNagaoUncond_sigma : k2PolyNagaoSigma_Statement :=
  ⟨bhNagaoUncond_sigmaWide, k2PolyNagaoWeyl_weylStatement⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_sigma

/-- The Nagao monodromy statement, unconditionally. -/
theorem bhNagaoUncond_mono : k2PolyNagao_MonoStatement :=
  k2PolyNagaoSigma_mono_of_statement bhNagaoUncond_sigma

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_mono

/-- The Euclid generation statement, unconditionally. -/
theorem bhNagaoUncond_euclidGen : k2PolyEuclid_GenStatement :=
  k2PolyNagao_gen_of_mono bhNagaoUncond_mono

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_euclidGen

/-- The normal-form coset statement, unconditionally. -/
theorem bhNagaoUncond_nfCoset : k2PolyNF_CosetStatement :=
  k2PolyEuclid_coset_of_gen bhNagaoUncond_euclidGen

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_nfCoset

/-- The normal-form stabilizer statement, unconditionally. -/
theorem bhNagaoUncond_nfStab : k2PolyNF_StabStatement :=
  k2PolyNF_stab_of_coset bhNagaoUncond_nfCoset

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_nfStab

/-- Every element of `K₂(N, F_p[X])`, `N ≥ 5`, is constant: unconditional. -/
theorem bhNagaoUncond_fieldConst :
    ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N → k2PolyField_ConstStatement (ZMod p) N :=
  k2PolyNF_const_of_stab bhNagaoUncond_nfStab

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_fieldConst

/-- The `n = 0` slice dies after padding, over every `ZMod p`: unconditional. -/
theorem bhNagaoUncond_nk2SliceDies_zero :
    ∀ p : ℕ, p.Prime → ElemFPCharZero.nk2Slice_DiesStatement (ZMod p) 0 :=
  ElemFPCharZero.k2PolyField_dies_zero_of_const fun p hp ↦ bhNagaoUncond_fieldConst p hp 5 le_rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_nk2SliceDies_zero

/-- The `n = 0` slice level statement, over every `ZMod p`: unconditional. -/
theorem bhNagaoUncond_nk2SliceLevel_zero :
    ∀ p : ℕ, p.Prime → ElemFPCharZero.nk2Slice_LevelStatement (ZMod p) 0 :=
  ElemFPCharZero.k2PolyField_level_zero_of_const fun p hp ↦
    bhNagaoUncond_fieldConst p hp 5 le_rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_nk2SliceLevel_zero

/-- Nagao for `F_p[s_0] = MvPolynomial (Fin 1) (ZMod p)`, unconditionally. -/
theorem bhNagaoUncond_K2_bot_mvFinOne {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    K2n N (MvPolynomial (Fin 1) (ZMod p)) = ⊥ :=
  bhNagaoWire_K2_bot_mvFinOne (k2PolyNagaoJRes_K2_bot hp hN)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_K2_bot_mvFinOne

/-- **The `k ≤ 1` slice of `PolynomialFpK2VanishingStatement`, unconditionally**:
`K₂(N, F_p[s_1..s_k]) = ⊥` for `k ≤ 1`, `N ≥ k + 4`, `N ≥ 5`.  `k = 0` is the field case,
`k = 1` is Nagao. -/
theorem bhNagaoUncond_polynomialFpK2Vanishing_le_one :
    ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k ≤ 1 → k + 4 ≤ N → 5 ≤ N →
      K2 (Fin N) (MvPolynomial (Fin k) (ZMod p)) = ⊥ := by
  intro p hp k N hk _ hN
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact bhNagaoWire_K2_bot_of_ringEquiv (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0))
      (vdkRowExt_fieldK2Vanishing p hp N hN)
  · exact bhNagaoUncond_K2_bot_mvFinOne hp hN

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_polynomialFpK2Vanishing_le_one

/-- **`E_N(F_p[s_1..s_k])` is finitely presented for `k ≤ 1`, `N ≥ k + 4`, unconditionally.**
The proof is that of `polynomialFpElementaryFP_of_polynomialFpK2Vanishing`, restricted to the
`k ≤ 1` slice. -/
theorem bhNagaoUncond_polynomialFpElementaryFP_le_one :
    ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k ≤ 1 → k + 4 ≤ N →
      Group.IsFinitelyPresented (elementaryGroup (Fin N) (MvPolynomial (Fin k) (ZMod p))) := by
  intro p hp k N hk hN
  rcases Nat.lt_or_ge N 5 with h4 | h5
  · obtain rfl : N = 4 := by omega
    obtain rfl : k = 0 := by omega
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Finite (MvPolynomial (Fin 0) (ZMod p)) :=
      Finite.of_equiv (ZMod p) (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).symm.toEquiv
    infer_instance
  · obtain ⟨d, rfl⟩ : ∃ d, N = d + 5 := ⟨N - 5, by omega⟩
    haveI := steinbergPoly_isFinitelyPresented p k d
    exact BooneHigman.SteinbergBasic.isFinitelyPresented_elementaryGroup_of_K2_eq_bot
      (bhNagaoUncond_polynomialFpK2Vanishing_le_one p hp k (d + 5) hk hN h5)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_polynomialFpElementaryFP_le_one

end GroupApproximation.BooneHigman.Metabelian.ElemFP
