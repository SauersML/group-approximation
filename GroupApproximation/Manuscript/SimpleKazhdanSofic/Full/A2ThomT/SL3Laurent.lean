import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.LaurentWidth
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.PropertyT.IntegralColumnPlaneClosure
import GroupApproximation.PropertyT.FinitelyGeneratedRing
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Meta.AxiomGuard
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Field.ZMod

/-!
# Property (T) for `SL_3(F_p[t,t⁻¹])`

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's group
`G_0(F_p[t,t⁻¹])` (A. Thom, Groups Geom. Dyn. 4 (2010), §2.1, Lemma 2.1) has property (T)
because it is built from copies of `SL_3(F_p[t,t⁻¹])`.

* `range_toGL_laurent`: over a field `K`, the image of `SL(3, K[t,t⁻¹])` in `GL` is the
  repository's elementary group `elementaryGroup (Fin 3) (K[t,t⁻¹])`. This is
  `mem_slElementary_three_laurent` (`SL_3 = E_3`) in the `EL_n` form.
* `sl3EquivElementary : SL(3, K[t,t⁻¹]) ≃* elementaryGroup (Fin 3) (K[t,t⁻¹])`.
* `hasKazhdanPropertyT_sl3Laurent p`: `SL(3, F_p[t,t⁻¹])` has property (T). This is the
  Ershov–Jaikin-Zapirain theorem for finitely generated rings as proved in the repository
  (`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`),
  transported along `sl3EquivElementary`.
-/

namespace GroupApproximation.Full.A2ThomT

section General

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The transvection `slTrans i k h c`, viewed in `GL`, is the repository's
`elementaryUnit i k h c`. -/
theorem slTrans_toGL (i k : n) (h : i ≠ k) (c : R) :
    Matrix.SpecialLinearGroup.toGL (slTrans i k h c) = elementaryUnit i k h c :=
  Units.ext rfl

/-- Transvection generators of `SL` map into the elementary group of `GL`. -/
theorem slElementary_le_comap_toGL :
    slElementary n R ≤ (elementaryGroup n R).comap Matrix.SpecialLinearGroup.toGL := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, k, h, c, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [slTrans_toGL]
  exact elementaryUnit_mem i k h c

/-- The elementary group of `GL` lies in the image of `SL`. -/
theorem elementaryGroup_le_range_toGL :
    elementaryGroup n R ≤
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n R).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, k, h, c, rfl⟩
  exact MonoidHom.mem_range.2 ⟨slTrans i k h c, slTrans_toGL i k h c⟩

end General

section Laurent

variable {K : Type*} [Field K]

/-- **`SL_3(K[t,t⁻¹]) = EL_3(K[t,t⁻¹])`** in the repository's `EL_n` form: the image of `SL`
in `GL` is `elementaryGroup (Fin 3) (K[t,t⁻¹])` (Thom, GGD 4 (2010), §2.1, Lemma 2.1, for
`K = F_p`; `simple_kazhdan_sofic_group.tex` l.57–59). -/
theorem range_toGL_laurent :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) (LaurentPolynomial K) →*
          Matrix.GeneralLinearGroup (Fin 3) (LaurentPolynomial K)).range =
      elementaryGroup (Fin 3) (LaurentPolynomial K) := by
  refine le_antisymm ?_ elementaryGroup_le_range_toGL
  intro x hx
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
  exact Subgroup.mem_comap.1 (slElementary_le_comap_toGL (mem_slElementary_three_laurent g))

/-- `SL(3, K[t,t⁻¹])` is isomorphic to the repository's elementary group
`elementaryGroup (Fin 3) (K[t,t⁻¹])`. -/
noncomputable def sl3EquivElementary :
    Matrix.SpecialLinearGroup (Fin 3) (LaurentPolynomial K) ≃*
      elementaryGroup (Fin 3) (LaurentPolynomial K) :=
  (MonoidHom.ofInjective
      (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := LaurentPolynomial K))).trans
    (MulEquiv.subgroupCongr range_toGL_laurent)

end Laurent

/-- `F_p[t,t⁻¹]` is a finitely generated ring. -/
theorem isFinitelyGeneratedRing_laurentZMod (p : ℕ) :
    IsFinitelyGeneratedRing (LaurentPolynomial (ZMod p)) :=
  (isFinitelyGeneratedRing_iff_finiteType_zmod p (LaurentPolynomial (ZMod p))).mpr
    (AddMonoidAlgebra.finiteType_of_fg (ZMod p) ℤ)

/-- **`SL(3, F_p[t,t⁻¹])` has Kazhdan's property (T).** Thom, GGD 4 (2010), §2.1, uses this for
the group `G_0(F_p[t,t⁻¹])`; `simple_kazhdan_sofic_group.tex` l.57–59. The proof combines
`SL_3 = EL_3` (`sl3EquivElementary`) with the Ershov–Jaikin-Zapirain theorem for the
finitely generated ring `F_p[t,t⁻¹]`. -/
theorem hasKazhdanPropertyT_sl3Laurent (p : ℕ) [Fact p.Prime] :
    HasKazhdanPropertyT.{0, 0}
      (Matrix.SpecialLinearGroup (Fin 3) (LaurentPolynomial (ZMod p))) :=
  (HasKazhdanPropertyT.mulEquiv_iff (sl3EquivElementary (K := ZMod p))).2
    (IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT
      (LaurentPolynomial (ZMod p)) (isFinitelyGeneratedRing_laurentZMod p) 3 le_rfl)

#audit_axioms hasKazhdanPropertyT_sl3Laurent

end GroupApproximation.Full.A2ThomT
