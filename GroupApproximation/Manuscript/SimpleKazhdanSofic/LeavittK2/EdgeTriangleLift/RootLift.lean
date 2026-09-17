import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.Bridge
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionInterfaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Edge and triangle lifts IV: the section lifts the roots (lane sk-leavitt-13)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  Lane 05's section
`VertexLift.sectionJ g = liftGL (H g) · rowVec (b g)`, for `g = [[H, 0], [b, 1]] ∈ J`, sends
`1 + E_{ij}(a)` (`j ≠ 3`) to `x_{ij}(a)` (`liftsRoots_sectionJ`).

* If `i ≠ 3`, the block is `1 + E_{ij}(a)` in `GL_3(L)` and the bottom row vanishes.  So
  `sectionJ` gives `liftGL (projection x_{ij}(a)) = stab x_{ij}(a) = x_{ij}(a)`.
* If `i = 3`, the block is `1` and the bottom row is `a e_j`, so `sectionJ` gives
  `rowVec (a e_j) = x_{3j}(a)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion
open scoped Matrix

/-- The upper block of `1 + E_{ij}(a)`, for `i, j < 3`. -/
theorem blockUnits_eu_castSucc (i j : Fin 3) (hij : i.castSucc ≠ j.castSucc) (hij' : i ≠ j)
    (a : BinL) {hm : elementaryUnit i.castSucc j.castSucc hij a ∈ vertexStab} :
    VertexLift.blockUnits ⟨elementaryUnit i.castSucc j.castSucc hij a, hm⟩ =
      elementaryUnit i j hij' a := by
  apply Units.ext
  ext k l
  show (1 + Matrix.single i.castSucc j.castSucc a : Matrix (Fin 4) (Fin 4) BinL)
      k.castSucc l.castSucc = (1 + Matrix.single i j a : Matrix (Fin 3) (Fin 3) BinL) k l
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.castSucc_inj]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.blockUnits_eu_castSucc

/-- The upper block of `1 + E_{3j}(a)` is `1`. -/
theorem blockUnits_eu_last (j : Fin 3) (a : BinL) (hne : (3 : Fin 4) ≠ j.castSucc)
    {hm : elementaryUnit (3 : Fin 4) j.castSucc hne a ∈ vertexStab} :
    VertexLift.blockUnits ⟨elementaryUnit (3 : Fin 4) j.castSucc hne a, hm⟩ = 1 := by
  apply Units.ext
  ext k l
  show (1 + Matrix.single (3 : Fin 4) j.castSucc a : Matrix (Fin 4) (Fin 4) BinL)
      k.castSucc l.castSucc = (1 : Matrix (Fin 3) (Fin 3) BinL) k l
  have h3k : (3 : Fin 4) ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
  simp only [Matrix.add_apply, Matrix.single_apply_of_row_ne h3k, add_zero, Matrix.one_apply,
    Fin.castSucc_inj]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.blockUnits_eu_last

/-- The bottom row of `1 + E_{ij}(a)`, for `i < 3`, vanishes. -/
theorem bottomRow_eu_castSucc (i : Fin 3) (j : Fin 4) (hij : i.castSucc ≠ j) (a : BinL)
    {hm : elementaryUnit i.castSucc j hij a ∈ vertexStab} :
    VertexLift.bottomRow ⟨elementaryUnit i.castSucc j hij a, hm⟩ = 0 := by
  funext k
  show (1 + Matrix.single i.castSucc j a : Matrix (Fin 4) (Fin 4) BinL) (3 : Fin 4) k.castSucc =
    (0 : Fin 3 → BinL) k
  have h3k : (3 : Fin 4) ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
  have hi3 : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
  rw [Matrix.add_apply, Matrix.one_apply_ne h3k, Matrix.single_apply_of_row_ne hi3, zero_add,
    Pi.zero_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.bottomRow_eu_castSucc

/-- The bottom row of `1 + E_{3j}(a)` is `a e_j`. -/
theorem bottomRow_eu_last (j : Fin 3) (a : BinL) (hne : (3 : Fin 4) ≠ j.castSucc)
    {hm : elementaryUnit (3 : Fin 4) j.castSucc hne a ∈ vertexStab} :
    VertexLift.bottomRow ⟨elementaryUnit (3 : Fin 4) j.castSucc hne a, hm⟩ = Pi.single j a := by
  funext k
  show (1 + Matrix.single (3 : Fin 4) j.castSucc a : Matrix (Fin 4) (Fin 4) BinL) (3 : Fin 4)
    k.castSucc = Pi.single j a k
  have h3k : (3 : Fin 4) ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
  rw [Matrix.add_apply, Matrix.one_apply_ne h3k, zero_add]
  by_cases hk : k = j
  · subst hk
    rw [Matrix.single_apply_same, Pi.single_eq_same]
  · have hjk : j.castSucc ≠ k.castSucc := fun h => hk (Fin.castSucc_inj.mp h).symm
    rw [Matrix.single_apply_of_col_ne _ _ hjk, Pi.single_eq_of_ne hk]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.bottomRow_eu_last

theorem fin3_cases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.fin3_cases

/-- `rowVec (a e_j) = x_{3j}(a)`. -/
theorem rowVec_single (j : Fin 3) (a : BinL) :
    VertexLift.rowVec (Pi.single j a) = x (Fin.last 3) j.castSucc (Fin.castSucc_ne_last j).symm a := by
  rcases fin3_cases j with rfl | rfl | rfl
  · have h1 : (1 : Fin 3) ≠ 0 := by decide
    have h2 : (2 : Fin 3) ≠ 0 := by decide
    simp only [VertexLift.rowVec, VertexLift.rowRoot, Pi.single_eq_same, Pi.single_eq_of_ne h1,
      Pi.single_eq_of_ne h2, x_zero, mul_one]
  · have h0 : (0 : Fin 3) ≠ 1 := by decide
    have h2 : (2 : Fin 3) ≠ 1 := by decide
    simp only [VertexLift.rowVec, VertexLift.rowRoot, Pi.single_eq_same, Pi.single_eq_of_ne h0,
      Pi.single_eq_of_ne h2, x_zero, one_mul, mul_one]
  · have h0 : (0 : Fin 3) ≠ 2 := by decide
    have h1 : (1 : Fin 3) ≠ 2 := by decide
    simp only [VertexLift.rowVec, VertexLift.rowRoot, Pi.single_eq_same, Pi.single_eq_of_ne h0,
      Pi.single_eq_of_ne h1, x_zero, one_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rowVec_single

/-- **Lane 05's section lifts the elementary roots.** -/
theorem liftsRoots_sectionJ (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : VertexLift.RowVecStabConjStatement) : LiftsRoots (VertexLift.sectionJ h hrow) := by
  intro i j hij hj a
  obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last (show j ≠ Fin.last 3 from hj)
  rw [VertexLift.sectionJ_apply]
  by_cases hi : i = 3
  · subst hi
    rw [bottomRow_eu_last j' a hij, blockUnits_eu_last j' a hij, map_one, one_mul]
    exact rowVec_single j' a
  · obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last (show i ≠ Fin.last 3 from hi)
    have hij' : i' ≠ j' := fun e => hij (congrArg Fin.castSucc e)
    rw [blockUnits_eu_castSucc i' j' hij hij' a, bottomRow_eu_castSucc i' _ hij a,
      VertexLift.rowVec_zero, mul_one]
    have hp : ((projection (x i' j' hij' a) : elementaryGroup (Fin 3) BinL) :
        (Matrix (Fin 3) (Fin 3) BinL)ˣ) = elementaryUnit i' j' hij' a := by
      rw [projection_x, elementaryRoot_val]
    rw [← hp, VertexLift.liftGL_projection, stab_x]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.liftsRoots_sectionJ

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
