import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Words
import GroupApproximation.Meta.AxiomGuard

/-!
# The Cohn path algebra `C_2` over a field

Lane `sk-leavitt-18`, first module.

`CohnTwo k` is the quotient of the free `k`-algebra on `e = s₀`, `f = s₁`,
`e* = t₀`, `f* = t₁` by the four Cohn relations `e*e = f*f = 1`,
`e*f = f*e = 0`. It is the binary Leavitt presentation
(`BinaryLeavitt.Relation`) with the relation `ee* + ff* = 1` dropped.

Route.
* `CohnTwo.data k` packages the four generators as a
  `CohnRelativeK1.CohnTwoData`, so that the words, the projection `p = 1 - ee* - ff*`,
  the matrix units `α p β*` and their multiplication rule come from lane
  `sk-leavitt-19` (`CohnRelativeK1/Words.lean`).
* `CohnTwo.toLeavitt : C_2 →ₐ L` is induced by the Leavitt quotient map. It is
  surjective (`toLeavitt_surjective`) and kills `p` (`toLeavitt_p`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- The four defining equations of the Cohn path algebra `C_2`:
`t₀s₀ = 1`, `t₀s₁ = 0`, `t₁s₀ = 0`, `t₁s₁ = 1`. -/
inductive CohnRelation (k : Type*) [Field k] :
    BinaryLeavitt.Free k → BinaryLeavitt.Free k → Prop
  | t0_s0 : CohnRelation k
      (FreeAlgebra.ι k BinaryLeavitt.t0 * FreeAlgebra.ι k BinaryLeavitt.s0) 1
  | t0_s1 : CohnRelation k
      (FreeAlgebra.ι k BinaryLeavitt.t0 * FreeAlgebra.ι k BinaryLeavitt.s1) 0
  | t1_s0 : CohnRelation k
      (FreeAlgebra.ι k BinaryLeavitt.t1 * FreeAlgebra.ι k BinaryLeavitt.s0) 0
  | t1_s1 : CohnRelation k
      (FreeAlgebra.ι k BinaryLeavitt.t1 * FreeAlgebra.ι k BinaryLeavitt.s1) 1

/-- The Cohn path algebra `C_2 = k⟨e, f, e*, f* | e*e = f*f = 1, e*f = f*e = 0⟩`. -/
abbrev CohnTwo (k : Type*) [Field k] := RingQuot (CohnRelation k)

namespace CohnTwo

variable (k : Type*) [Field k]

/-- The quotient map from noncommutative polynomials onto `C_2`. -/
def quotientMap : BinaryLeavitt.Free k →ₐ[k] CohnTwo k :=
  RingQuot.mkAlgHom k (CohnRelation k)

/-- A named generator of `C_2`. -/
def generator (g : BinaryLeavitt.Generator) : CohnTwo k :=
  quotientMap k (FreeAlgebra.ι k g)

theorem quotientMap_surjective : Function.Surjective (quotientMap k) :=
  RingQuot.mkAlgHom_surjective k (CohnRelation k)

/-- The Cohn relations in `C_2`, packaged for the word calculus of lane 19. -/
def data : CohnRelativeK1.CohnTwoData (CohnTwo k) where
  e := generator k BinaryLeavitt.s0
  f := generator k BinaryLeavitt.s1
  es := generator k BinaryLeavitt.t0
  fs := generator k BinaryLeavitt.t1
  es_e := by
    have h := RingQuot.mkAlgHom_rel k (CohnRelation.t0_s0 (k := k))
    rw [map_mul, map_one] at h
    exact h
  fs_f := by
    have h := RingQuot.mkAlgHom_rel k (CohnRelation.t1_s1 (k := k))
    rw [map_mul, map_one] at h
    exact h
  es_f := by
    have h := RingQuot.mkAlgHom_rel k (CohnRelation.t0_s1 (k := k))
    rw [map_mul, map_zero] at h
    exact h
  fs_e := by
    have h := RingQuot.mkAlgHom_rel k (CohnRelation.t1_s0 (k := k))
    rw [map_mul, map_zero] at h
    exact h

/-- The projection `p = 1 - ee* - ff*` of `C_2`. -/
abbrev cohnP : CohnTwo k := (data k).p

theorem cohnP_eq : cohnP k =
    1 - generator k BinaryLeavitt.s0 * generator k BinaryLeavitt.t0 -
      generator k BinaryLeavitt.s1 * generator k BinaryLeavitt.t1 := rfl

theorem toLeavitt_respects :
    ∀ ⦃x y : BinaryLeavitt.Free k⦄, CohnRelation k x y →
      BinaryLeavitt.quotientMap k x = BinaryLeavitt.quotientMap k y := by
  intro x y h
  cases h
  · exact RingQuot.mkAlgHom_rel k (BinaryLeavitt.Relation.t0_s0 (k := k))
  · exact RingQuot.mkAlgHom_rel k (BinaryLeavitt.Relation.t0_s1 (k := k))
  · exact RingQuot.mkAlgHom_rel k (BinaryLeavitt.Relation.t1_s0 (k := k))
  · exact RingQuot.mkAlgHom_rel k (BinaryLeavitt.Relation.t1_s1 (k := k))

/-- The canonical surjection `C_2 → L_k(1,2)`. -/
def toLeavitt : CohnTwo k →ₐ[k] BinaryLeavitt.BinaryLeavittAlgebra k :=
  RingQuot.liftAlgHom k ⟨BinaryLeavitt.quotientMap k, toLeavitt_respects k⟩

theorem toLeavitt_quotientMap (x : BinaryLeavitt.Free k) :
    toLeavitt k (quotientMap k x) = BinaryLeavitt.quotientMap k x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k (BinaryLeavitt.quotientMap k) (toLeavitt_respects k) x

theorem toLeavitt_generator (g : BinaryLeavitt.Generator) :
    toLeavitt k (generator k g) = BinaryLeavitt.generator k g :=
  toLeavitt_quotientMap k (FreeAlgebra.ι k g)

theorem toLeavitt_surjective : Function.Surjective (toLeavitt k) := by
  intro y
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (BinaryLeavitt.Relation k) y
  exact ⟨quotientMap k x, toLeavitt_quotientMap k x⟩

theorem toLeavitt_p : toLeavitt k (cohnP k) = 0 := by
  have h :
      BinaryLeavitt.generator k BinaryLeavitt.s0 * BinaryLeavitt.generator k BinaryLeavitt.t0 +
        BinaryLeavitt.generator k BinaryLeavitt.s1 * BinaryLeavitt.generator k BinaryLeavitt.t1 = 1 :=
    (BinaryLeavitt.family k).sum_range
  rw [cohnP_eq, map_sub, map_sub, map_one, map_mul, map_mul, toLeavitt_generator,
    toLeavitt_generator, toLeavitt_generator, toLeavitt_generator, sub_sub, h, sub_self]

end CohnTwo

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelation
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.generator
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientMap_surjective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.data
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.cohnP
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.cohnP_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt_respects
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt_quotientMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt_generator
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt_surjective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.toLeavitt_p
