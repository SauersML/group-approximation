import GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTeleCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The variable telescope for `ker ev₀` on `K₂(I, A[t_0..t_{k-1}])`

Lane `bh-met-95b`, telescope module.  `A` is any commutative ring and `I` any finite index type.
Write `B_j = A[t_0..t_{j-1}]` and `ev₀ : B_j → A` for the evaluation at `0` (`constantCoeff`).

**The filtration.**  Under `MvPolynomial.finSuccEquiv`, `B_{j+1} ≅ B_j[t]`, and `ev₀` on `B_{j+1}`
is `ev₀ ∘ (t ↦ 0)`.  The graded piece of step `j` is

  `NK₂(I, B_j) = ker (K₂(I, B_j[t]) → K₂(I, B_j))`, the kernel of `t ↦ 0`.

* `fg_ker_constantCoeff_succ`: `ker ev₀` on `K₂(I, B_{j+1})` is finitely generated once `ker ev₀`
  on `K₂(I, B_j)` and the graded piece `NK₂(I, B_j)` are (the split `fg_ker_K2Map_of_split`,
  then transport along `finSuccEquiv` by `fg_ker_K2Map_of_retract`).
* `fg_ker_constantCoeff_of_steps` (**the telescope**): if every graded piece `NK₂(I, B_j)`,
  `j < k`, is finitely generated, so is `ker ev₀` on `K₂(I, B_k)`.  The base `k = 0` is
  `ElemFP.K2Map_constantCoeff_injective_of_isEmpty`.
* `fg_ker_evalZero_of_le` (**dummy variables**): for `j ≤ j'`, `NK₂(I, B_j)` is a retract of
  `NK₂(I, B_{j'})` (through `rename` and `killCompl` of `Fin.castLE`, applied coefficientwise),
  so its finite generation follows.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section EvalMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluation at `0` commutes with coefficient maps. -/
theorem evalRingHom_zero_comp_mapRingHom (f : R →+* S) :
    (Polynomial.evalRingHom 0 : Polynomial S →+* S).comp (Polynomial.mapRingHom f) =
      f.comp (Polynomial.evalRingHom 0) :=
  RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom, Polynomial.eval_zero_map]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.evalRingHom_zero_comp_mapRingHom

end EvalMap

section Telescope

variable (A : Type*) [CommRing A] (I : Type*) [Fintype I] [DecidableEq I]

/-- **One step of the telescope.**  `ker ev₀` on `K₂(I, A[t_0..t_k])` is finitely generated
once `ker ev₀` on `K₂(I, A[t_0..t_{k-1}])` and the graded piece
`ker (K₂(I, A[t_0..t_{k-1}][t]) → K₂(I, A[t_0..t_{k-1}]))` are. -/
theorem fg_ker_constantCoeff_succ (k : ℕ)
    (hk : Group.FG
      (K2Map (I := I) (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A)).ker)
    (hstep : Group.FG (K2Map (I := I)
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A)).ker) :
    Group.FG (K2Map (I := I)
      (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A)).ker := by
  have hpoly : Group.FG (K2Map (I := I)
      ((MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A).comp
        (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A))).ker :=
    fg_ker_K2Map_of_split
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A)
      Polynomial.C evalRingHom_zero_comp_C
      ((MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A).comp
        (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A))
      MvPolynomial.constantCoeff rfl hk hstep
  refine fg_ker_K2Map_of_retract _ _
    (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm.toRingHom
    (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom (RingHom.id A) (RingHom.id A)
    (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm_toRingHom_comp_toRingHom ?_ ?_ hpoly
  · rw [RingHom.id_comp, ← constantCoeff_comp_finSuccEquiv (R := A) k, RingHom.comp_assoc,
      RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id]
  · rw [RingHom.id_comp]
    exact constantCoeff_comp_finSuccEquiv k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.fg_ker_constantCoeff_succ

/-- **The telescope.**  If every graded piece
`ker (K₂(I, A[t_0..t_{j-1}][t]) → K₂(I, A[t_0..t_{j-1}]))`, `j < k`, is finitely generated, then
the kernel of `ev₀ : K₂(I, A[t_0..t_{k-1}]) → K₂(I, A)` is finitely generated. -/
theorem fg_ker_constantCoeff_of_steps : ∀ k : ℕ,
    (∀ j : ℕ, j < k → Group.FG (K2Map (I := I)
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin j) A) →+* MvPolynomial (Fin j) A)).ker) →
    Group.FG (K2Map (I := I)
      (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A)).ker := by
  intro k
  induction k with
  | zero =>
    intro _
    have hker : (K2Map (I := I)
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 0) A →+* A)).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr K2Map_constantCoeff_injective_of_isEmpty
    rw [Group.fg_iff_subgroup_fg, hker]
    exact Subgroup.FG.bot
  | succ k ih =>
    intro hsteps
    exact fg_ker_constantCoeff_succ A I k (ih fun j hj ↦ hsteps j (by omega))
      (hsteps k (by omega))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.fg_ker_constantCoeff_of_steps

/-- **Dummy variables.**  For `j ≤ j'`, the graded piece over `A[t_0..t_{j-1}]` is a retract of
the graded piece over `A[t_0..t_{j'-1}]`, so it is finitely generated when the latter is. -/
theorem fg_ker_evalZero_of_le {j j' : ℕ} (h : j ≤ j')
    (hbig : Group.FG (K2Map (I := I)
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin j') A) →+* MvPolynomial (Fin j') A)).ker) :
    Group.FG (K2Map (I := I)
      (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin j) A) →+* MvPolynomial (Fin j) A)).ker := by
  have hPQ₀ : (MvPolynomial.killCompl (R := A) (Fin.castLE_injective h)).toRingHom.comp
      (MvPolynomial.rename (R := A) (Fin.castLE h)).toRingHom = RingHom.id _ :=
    RingHom.ext fun x ↦ MvPolynomial.killCompl_rename_app (Fin.castLE_injective h) x
  refine fg_ker_K2Map_of_retract _ _
    (Polynomial.mapRingHom (MvPolynomial.killCompl (R := A) (Fin.castLE_injective h)).toRingHom)
    (Polynomial.mapRingHom (MvPolynomial.rename (R := A) (Fin.castLE h)).toRingHom)
    (MvPolynomial.killCompl (R := A) (Fin.castLE_injective h)).toRingHom
    (MvPolynomial.rename (R := A) (Fin.castLE h)).toRingHom ?_
    (evalRingHom_zero_comp_mapRingHom _) (evalRingHom_zero_comp_mapRingHom _) hbig
  rw [Polynomial.mapRingHom_comp, hPQ₀, Polynomial.mapRingHom_id]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.fg_ker_evalZero_of_le

end Telescope

end GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele
