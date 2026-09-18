import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseComplement
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import GroupApproximation.Analysis.CStarQuotientHom

/-!
# The compact ideal of `𝓛(H_J)` and the Busby map into the corona

Lane `TWWSch-Inv1`, work order `WO-Inv-1`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership`, through the Busby picture of `Ext(S, J)` in Schafhauser's proof
of the Tikuisis--White--Winter theorem.

The Choi--Effros lifting theorem (M.-D. Choi, E. G. Effros, *The completely positive lifting
problem for C⋆-algebras*, Ann. of Math. (2) **104** (1976), Thm. 3.10; Brown--Ozawa,
*C⋆-algebras and finite-dimensional approximations*, Thm. C.3) is applied to the quotient map
`𝓛(H_J) → 𝓛(H_J)/𝒦(H_J)`, as in Arveson, Duke Math. J. **44** (1977), §4. This file supplies
the algebraic side of that application:

* `stdCptIdeal J`: the compact operators, a two-sided ideal of `StdBdd J`, star-stable and
  norm-closed (`stdCptIdeal_isTwoSided`, `stdCptIdeal_isStarStable`, `stdCptIdeal_isClosed`);
* `mk_eq_mk_iff_compactEq`: equality in the quotient is `CompactEq`;
* `BusbyCycle.liftBdd` and **`BusbyCycle.toCorona`**: a Busby cycle is a genuine
  `⋆`-homomorphism `S → StdBdd J ⧸ stdCptIdeal J`.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Ideal

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

variable (J) in
/-- **The compact operators on `H_J`**, as an ideal of the bounded operators
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance, *Hilbert C⋆-modules*, Ch. 1). -/
def stdCptIdeal : Ideal (StdBdd J) where
  carrier := {T | T.1.IsCompactOp}
  add_mem' := fun {T U} hT hU =>
    show (T + U).1.IsCompactOp from Adjointable.IsCompactOp.add (T := T.1) (S := U.1) hT hU
  zero_mem' := Adjointable.isCompactOp_zero (E := standardModule ℕ J) (F := standardModule ℕ J)
  smul_mem' := fun c {T} hT =>
    show (c * T).1.IsCompactOp from
      Adjointable.IsCompactOp.comp_left (T := T.1) hT (StdBdd.isBounded c)

/-- Membership in the compact ideal (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem mem_stdCptIdeal (T : StdBdd J) : T ∈ stdCptIdeal J ↔ T.1.IsCompactOp := Iff.rfl

/-- The compact ideal is two-sided (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
instance stdCptIdeal_isTwoSided : (stdCptIdeal J).IsTwoSided where
  mul_mem_of_left {T} U hT :=
    (mem_stdCptIdeal (T * U)).mpr (((mem_stdCptIdeal T).mp hT).comp_right (StdBdd.isBounded U))

/-- The compact ideal is star-stable (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
instance stdCptIdeal_isStarStable : CStarTensor.IsStarStable (stdCptIdeal J) where
  star_mem {T} hT :=
    (mem_stdCptIdeal (star T)).mpr (Adjointable.IsCompactOp.adjoint ((mem_stdCptIdeal T).mp hT))

/-- **The compact ideal is norm-closed**: a norm limit of compact operators is compact
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
instance stdCptIdeal_isClosed : IsClosed (stdCptIdeal J : Set (StdBdd J)) := by
  refine isClosed_of_closure_subset fun T hT => ?_
  rw [Metric.mem_closure_iff] at hT
  refine Adjointable.isCompactOp_of_approx (StdBdd.isBounded T) fun ε hε => ?_
  obtain ⟨K, hK, hTK⟩ := hT ε hε
  refine ⟨K.1, (mem_stdCptIdeal K).mp (SetLike.mem_coe.mp hK), ?_⟩
  have h1 : (T - K).1.opNorm ≤ ε := by
    have h2 : ‖T - K‖ < ε := by
      rw [dist_eq_norm] at hTK
      exact hTK
    exact h2.le
  exact (Adjointable.isBoundedBy_opNorm (StdBdd.isBounded (T - K))).mono h1

/-- **Equality in the corona is equality modulo compacts** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem mk_eq_mk_iff_compactEq (T U : StdBdd J) :
    Ideal.Quotient.mk (stdCptIdeal J) T = Ideal.Quotient.mk (stdCptIdeal J) U ↔
      CompactEq J T.1 U.1 :=
  Ideal.Quotient.eq.trans Iff.rfl

end Ideal

section Corona

variable {S : Type} [NonUnitalCStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The lift of a Busby cycle, as an element of the bounded operators (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
def BusbyCycle.liftBdd (x : BusbyCycle S J) (a : S) : StdBdd J :=
  ⟨x.lift a, mem_boundedAdj.mpr (x.bounded a)⟩

/-- The underlying operator of `liftBdd` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem BusbyCycle.liftBdd_coe (x : BusbyCycle S J) (a : S) : (x.liftBdd a).1 = x.lift a := rfl

/-- Additivity in the corona (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem BusbyCycle.mk_liftBdd_add (x : BusbyCycle S J) (a a' : S) :
    Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd (a + a')) =
      Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a) +
        Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a') :=
  ((mk_eq_mk_iff_compactEq (x.liftBdd (a + a')) (x.liftBdd a + x.liftBdd a')).mpr
    (x.map_add a a')).trans (map_add (Ideal.Quotient.mk (stdCptIdeal J)) _ _)

/-- Multiplicativity in the corona (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem BusbyCycle.mk_liftBdd_mul (x : BusbyCycle S J) (a a' : S) :
    Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd (a * a')) =
      Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a) *
        Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a') :=
  ((mk_eq_mk_iff_compactEq (x.liftBdd (a * a')) (x.liftBdd a * x.liftBdd a')).mpr
    (x.map_mul a a')).trans (map_mul (Ideal.Quotient.mk (stdCptIdeal J)) _ _)

/-- Linearity in the corona (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem BusbyCycle.mk_liftBdd_smul (x : BusbyCycle S J) (c : ℂ) (a : S) :
    Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd (c • a)) =
      c • Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a) :=
  ((mk_eq_mk_iff_compactEq (x.liftBdd (c • a)) (c • x.liftBdd a)).mpr
    (x.map_smul c a)).trans (CStarTensor.quotient_mk_smul (stdCptIdeal J) c (x.liftBdd a))

/-- The involution in the corona (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem BusbyCycle.mk_liftBdd_star (x : BusbyCycle S J) (a : S) :
    Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd (star a)) =
      star (Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a)) :=
  ((mk_eq_mk_iff_compactEq (x.liftBdd (star a)) (star (x.liftBdd a))).mpr
    (x.map_star a)).trans (CStarTensor.quotient_star_mk (stdCptIdeal J) (x.liftBdd a)).symm

/-- **The Busby map of a cycle**, a `⋆`-homomorphism into the corona algebra
`StdBdd J ⧸ stdCptIdeal J` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Arveson, Duke Math. J. 44 (1977), §4). -/
def BusbyCycle.toCorona (x : BusbyCycle S J) : S →⋆ₙₐ[ℂ] StdBdd J ⧸ stdCptIdeal J where
  toFun a := Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a)
  map_smul' c a := x.mk_liftBdd_smul c a
  map_zero' := by
    have h := x.mk_liftBdd_add 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  map_add' a a' := x.mk_liftBdd_add a a'
  map_mul' a a' := x.mk_liftBdd_mul a a'
  map_star' a := x.mk_liftBdd_star a

/-- The Busby map on an element (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem BusbyCycle.toCorona_apply (x : BusbyCycle S J) (a : S) :
    x.toCorona a = Ideal.Quotient.mk (stdCptIdeal J) (x.liftBdd a) := rfl

end Corona

end GroupApproximation.Full.TWWSchafhauser

end
