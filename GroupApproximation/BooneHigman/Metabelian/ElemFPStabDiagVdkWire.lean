import GroupApproximation.BooneHigman.Metabelian.ElemFPStabDiagVdkBase
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilCharP
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal stability on `ker ev₀`: the `k ≥ 2` residual

Lane `bh-met-96`, part 2 of 3.  Write `R_k = F_p[s_1..s_k] = MvPolynomial (Fin k) (ZMod p)`.

* `stabDiagVdk_GeTwoStatement`: **the residual**.  It is `PolyK2StabRangeDiagStatement`
  restricted to `k ≥ 2`: an element `u ∈ K₂(k + 4, R_k)` with `ev₀ u = 1` and
  `K2Stab u = 1` is trivial.
* `stabDiagVdk_polyK2StabRangeDiag_of_geTwo`: **endpoint**.  The residual gives the whole
  target: the missing instance `k = 1` is `stabDiagVdk_diag_one` (Nagao).
* `stabDiagVdk_geTwo_of_noHiddenRel`: the residual from `ker Π = ⊥`
  (`vdkParPres_NoHiddenRel (k + 4) R_k`, lane `bh-met-92g`) for `k ≥ 2`.  This is the precise
  `ker Π = ⊥` statement the diagonal target needs (not `ker Π = ⊥` over `F_p[s]` alone).
* `stabDiagVdk_nilGapOver_of_geTwo`, `stabDiagVdk_polynomialFpK2Vanishing_of_geTwo`: `P1` and
  the `F_p` vanishing from the OneVarNil conjunct and the residual.

**LOUD (strength).**  The residual is *provably equivalent* to the target
(`stabDiagVdk_geTwo_iff`): the forward direction is weakening, the backward one uses the proved
`k = 1` instance.  It is strictly smaller only in **proof content** (the base instance `k = 1`
is discharged, by Nagao).  Every instance `k ≥ 2` is still open.

Why the `finSuccEquiv` induction does not close it.  `R_{k+1} ≅ R_k[t]`, and the step would
have to compare `K₂(k + 5, R_k[t])` with `K₂(k + 5, R_k)`.  That is the nil part `NK₂(R_k) = 0`
(Quillen), which Nagao's amalgam gives only over a *field* base (`R_0 = F_p`).  Moreover the
rank goes up with `k`.  The retraction `R_k → R_{k'}` (`eq_one_of_K2Stab_retract`) moves the
statement to more variables at the *same* rank, i.e. out of the diagonal.  So the `k ≥ 2`
instances need genuine injective stability over `R_k` (van der Kallen, `n ≥ sr + 2`).

Truth.  By Bass, `sr(R_k) ≤ k + 1` (proved here as `vdkSR_stableRangeLE_mvPolynomial`); van der
Kallen's theorem makes `K2Stab (k + 4) R_k` injective, since `k + 4 ≥ sr + 3`.  So the residual
and the `ker Π = ⊥` input of `stabDiagVdk_geTwo_of_noHiddenRel` are true.  Neither is proved.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Residual** (lane `bh-met-96`): diagonal injective stability on `ker ev₀` for `k ≥ 2`.
LOUD: provably equivalent to `PolyK2StabRangeDiagStatement` (`stabDiagVdk_geTwo_iff`); smaller
only in proof content (the `k = 1` instance is Nagao). -/
def stabDiagVdk_GeTwoStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k →
    ∀ u : K2n (k + 4) (MvPolynomial (Fin k) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab (k + 4) (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_GeTwoStatement

/-- **Endpoint**: the `k ≥ 2` residual gives `PolyK2StabRangeDiagStatement`.  The instance
`k = 1` is `stabDiagVdk_diag_one`. -/
theorem stabDiagVdk_polyK2StabRangeDiag_of_geTwo (h : stabDiagVdk_GeTwoStatement) :
    PolyK2StabRangeDiagStatement := by
  intro p hp k hk u hu0 hu
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    exact stabDiagVdk_diag_one p hp u hu0 hu
  · exact h p hp k hk2 u hu0 hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_polyK2StabRangeDiag_of_geTwo

/-- The target gives the residual back (weakening). -/
theorem stabDiagVdk_geTwo_of_polyK2StabRangeDiag (h : PolyK2StabRangeDiagStatement) :
    stabDiagVdk_GeTwoStatement :=
  fun p hp k hk ↦ h p hp k (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_geTwo_of_polyK2StabRangeDiag

/-- **LOUD (strength)**: the residual is equivalent to the target. -/
theorem stabDiagVdk_geTwo_iff : stabDiagVdk_GeTwoStatement ↔ PolyK2StabRangeDiagStatement :=
  ⟨stabDiagVdk_polyK2StabRangeDiag_of_geTwo, stabDiagVdk_geTwo_of_polyK2StabRangeDiag⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_geTwo_iff

/-- **The `ker Π = ⊥` form**: no hidden relations in the parabolic presentation over `R_k` at
rank `k + 4`, for `k ≥ 2`, gives the residual.  Instancewise this input is stronger than the
residual (injectivity of `K2Stab` everywhere, not only on `ker ev₀`), and true by van der
Kallen. -/
theorem stabDiagVdk_geTwo_of_noHiddenRel
    (h : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k →
      vdkParPres_NoHiddenRel (k + 4) (MvPolynomial (Fin k) (ZMod p))) :
    stabDiagVdk_GeTwoStatement :=
  fun p hp k hk u _ hu ↦
    (injective_iff_map_eq_one (K2Stab (k + 4) (MvPolynomial (Fin k) (ZMod p)))).mp
      (vdkParPres_noHiddenRel_iff_K2Stab_injective.mp (h p hp k hk)) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_geTwo_of_noHiddenRel

/-- **`P1` from the OneVarNil conjunct and the `k ≥ 2` residual.** -/
theorem stabDiagVdk_nilGapOver_of_geTwo (hone : PolyK2OneVarNilStatement)
    (h : stabDiagVdk_GeTwoStatement) :
    ∀ p : ℕ, p.Prime → PolyK2NilGapStatementOver (ZMod p) 4 :=
  fun p hp ↦ ⟨polyK2OneVarNil_iff_forall_over.mp hone p hp,
    polyK2StabRangeDiag_iff_forall_over.mp (stabDiagVdk_polyK2StabRangeDiag_of_geTwo h) p hp⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_nilGapOver_of_geTwo

/-- **The `F_p` vanishing** `K₂(N, F_p[s_1..s_k]) = ⊥` (`N ≥ k + 4`, `N ≥ 5`) from the
OneVarNil conjunct and the `k ≥ 2` residual; the field case is `vdkRowExt_fieldK2Vanishing`. -/
theorem stabDiagVdk_polynomialFpK2Vanishing_of_geTwo (hone : PolyK2OneVarNilStatement)
    (h : stabDiagVdk_GeTwoStatement) : PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_gapOver (stabDiagVdk_nilGapOver_of_geTwo hone h)
    vdkRowExt_fieldK2Vanishing

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_polynomialFpK2Vanishing_of_geTwo

end GroupApproximation.BooneHigman.Metabelian.ElemFP
