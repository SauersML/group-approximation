import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split
import GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTeleTelescope
import GroupApproximation.Meta.AxiomGuard

/-!
# `CharZeroK2NilFGPosStatement` from the graded pieces of the telescope

Lane `bh-met-95b`, endpoint.  Write `A = ℤ[1/m]` and `B_j = A[t_0..t_{j-1}]`.

**Residual.**  `CharZeroK2NilStepFGDiagStatement`: for all `m, j`, the one-variable nil piece
`NK₂(j + 5, B_j) = ker (ev₀ : K₂(j + 5, B_j[t]) → K₂(j + 5, B_j))` is finitely generated.  Only
one variable is killed, and only at the single diagonal rank `N = j + 5`.

**Reduction.**  `charZeroK2NilFGPos_of_stepFGDiag`: given `m`, `k ≥ 1` and `N ≥ k + 4`, `N ≥ 5`,
the telescope `fg_ker_constantCoeff_of_steps` reduces `ker ev₀` on `K₂(N, B_k)` to the pieces
`NK₂(N, B_j)`, `j < k`.  Since `j + 5 ≤ N`, each is a retract of `NK₂(N, B_{N-5})`
(`fg_ker_evalZero_of_le`), which is the residual at `j = N - 5`.

**Truth check.**  The residual is true: `B_j[t]` is regular of Krull dimension `≤ j + 2`, so at
rank `j + 5` the kernel is trivial (injective stability for `K₂` plus `NK₂ = 0` for regular
rings); for `m = 0` the ring is zero.  Formally, `charZeroK2NilStepFGDiag_of_nilPos` derives it
from the documented-true `CharZeroK2NilPosStatement`.

**What is gained.**  The residual keeps neither the induction on the number of variables, nor
the ranks `N > j + 5`, nor more than one variable at a time: the telescope and the dummy-variable
transfer are proved here.  (Its derivation *from* `CharZeroK2NilFGPosStatement` would use that
`K₂` is abelian, which is not formalized here.)
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP
open GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **Residual.**  The one-variable nil piece of `K₂(j + 5, ℤ[1/m][t_0..t_{j-1}])`, the kernel
of `t ↦ 0`, is finitely generated. -/
def CharZeroK2NilStepFGDiagStatement : Prop :=
  ∀ m j : ℕ, Group.FG (K2Map (I := Fin (j + 5))
    (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) (Localization.Away (m : ℤ))) →+*
        MvPolynomial (Fin j) (Localization.Away (m : ℤ)))).ker

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.CharZeroK2NilStepFGDiagStatement

/-- **Endpoint (lane `bh-met-95b`).**  The residual gives `CharZeroK2NilFGPosStatement`. -/
theorem charZeroK2NilFGPos_of_stepFGDiag (h : CharZeroK2NilStepFGDiagStatement) :
    CharZeroK2NilFGPosStatement := by
  intro m k N hk hkN h5N
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, N = j' + 5 := ⟨N - 5, by omega⟩
  refine fg_ker_constantCoeff_of_steps (Localization.Away (m : ℤ)) (Fin (j' + 5)) k
    fun j hj ↦ ?_
  exact fg_ker_evalZero_of_le (Localization.Away (m : ℤ)) (Fin (j' + 5)) (by omega) (h m j')

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.charZeroK2NilFGPos_of_stepFGDiag

/-- The split gap from the base part and the residual. -/
theorem splitGap_of_base_of_stepFGDiag (hbase : CharZeroK2BaseFGStatement)
    (h : CharZeroK2NilStepFGDiagStatement) : CharZeroK2SplitGapStatement :=
  ⟨hbase, charZeroK2NilFGPos_of_stepFGDiag h⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.splitGap_of_base_of_stepFGDiag

/-- `CharZeroStableK2FGStatement` from the base part and the residual. -/
theorem stableK2FG_of_base_of_stepFGDiag (hbase : CharZeroK2BaseFGStatement)
    (h : CharZeroK2NilStepFGDiagStatement) : CharZeroStableK2FGStatement :=
  charZeroStableK2FG_of_splitGap (splitGap_of_base_of_stepFGDiag hbase h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.stableK2FG_of_base_of_stepFGDiag

/-- **Truth check.**  The documented-true vanishing statement implies the residual, through
`B_{j+1} ≅ B_j[t]` (`MvPolynomial.finSuccEquiv`). -/
theorem charZeroK2NilStepFGDiag_of_nilPos (h : CharZeroK2NilPosStatement) :
    CharZeroK2NilStepFGDiagStatement := by
  intro m j
  have hker : (K2Map (I := Fin (j + 5))
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin j) (Localization.Away (m : ℤ))) →+*
          MvPolynomial (Fin j) (Localization.Away (m : ℤ)))).ker = ⊥ := by
    refine (MonoidHom.ker_eq_bot_iff _).mpr ((injective_iff_map_eq_one _).mpr fun u hu ↦ ?_)
    have hv := h m (j + 1) (j + 5) (Nat.succ_pos j) (by omega) (by omega)
      (K2Map (MvPolynomial.finSuccEquiv (Localization.Away (m : ℤ)) j).toRingEquiv.symm.toRingHom
        u)
      (by
        rw [← constantCoeff_comp_finSuccEquiv (R := Localization.Away (m : ℤ)) j,
          ← K2Map_K2Map, ← K2Map_K2Map, K2Map_K2Map_of_comp_eq_id _ _
            (MvPolynomial.finSuccEquiv (Localization.Away (m : ℤ))
              j).toRingEquiv.toRingHom_comp_symm_toRingHom,
          hu, map_one])
    rw [← K2Map_K2Map_of_comp_eq_id _ _ (MvPolynomial.finSuccEquiv (Localization.Away (m : ℤ))
      j).toRingEquiv.toRingHom_comp_symm_toRingHom u, hv, map_one]
  rw [Group.fg_iff_subgroup_fg, hker]
  exact Subgroup.FG.bot

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.charZeroK2NilStepFGDiag_of_nilPos

end GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele
