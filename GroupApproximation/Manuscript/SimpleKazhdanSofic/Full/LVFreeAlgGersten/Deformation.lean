import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.Augmented
import GroupApproximation.Meta.AxiomGuard

/-!
# The scaling deformation of a free algebra (lane sk-ger-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.

For a commutative ring `F` and a type `V`, the free algebra `F⟨V⟩` carries the scaling
deformation `ψ : F⟨V⟩ → F⟨V⟩[t]`, `xᵢ ↦ xᵢ t` (Swan–Weibel).  Its two ends are

* `(t ↦ 0) ∘ ψ = const ∘ aug` (`skGer_constantCoeff_comp_deform`), and
* `(t ↦ 1) ∘ ψ = id` (`skGer_evalOne_comp_deform`).

Here `t ↦ 0` is `Polynomial.constantCoeff` and `t ↦ 1` is the noncommutative evaluation
`skGer_evalOne` (the variable `t` is central, so `1` commutes with every coefficient).
We also record the constant-coefficient square `F[t] → F⟨V⟩[t]` used to compare with the
polynomial ring `F[t]`.
-/

namespace GroupApproximation.Full.LVFreeAlgGersten

noncomputable section

section EvalOne

variable (R : Type*) [Ring R]

/-- Evaluation at `t = 1` of polynomials over a possibly noncommutative ring.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skGer_evalOne : Polynomial R →+* R :=
  Polynomial.eval₂RingHom' (RingHom.id R) 1 fun a => Commute.one_right ((RingHom.id R) a)

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne

/-- `skGer_evalOne` is `eval₂ id 1`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_evalOne_apply (p : Polynomial R) :
    skGer_evalOne R p = Polynomial.eval₂ (RingHom.id R) 1 p :=
  rfl

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne_apply

/-- Evaluation at `t = 1` of a constant.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_evalOne_C (a : R) : skGer_evalOne R (Polynomial.C a) = a := by
  rw [skGer_evalOne_apply]
  exact Polynomial.eval₂_C (RingHom.id R) 1

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne_C

/-- Evaluation at `t = 1` of the variable.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_evalOne_X : skGer_evalOne R (Polynomial.X : Polynomial R) = 1 := by
  rw [skGer_evalOne_apply]
  exact Polynomial.eval₂_X (RingHom.id R) 1

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne_X

end EvalOne

section Deform

variable (F V : Type*) [CommRing F]

/-- The generators of the deformation: `xᵢ ↦ xᵢ t`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skGer_deformGen : V → Polynomial (FreeAlgebra F V) :=
  fun i => Polynomial.C (FreeAlgebra.ι F i) * Polynomial.X

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_deformGen

/-- The scaling deformation `F⟨V⟩ → F⟨V⟩[t]` as an `F`-algebra map.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skGer_deformAlg : FreeAlgebra F V →ₐ[F] Polynomial (FreeAlgebra F V) :=
  FreeAlgebra.lift F (skGer_deformGen F V)

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_deformAlg

/-- The scaling deformation `ψ : F⟨V⟩ → F⟨V⟩[t]`, `xᵢ ↦ xᵢ t`, as a ring map.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skGer_deform : FreeAlgebra F V →+* Polynomial (FreeAlgebra F V) :=
  (skGer_deformAlg F V).toRingHom

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_deform

/-- The deformation on a generator.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_deform_ι (i : V) :
    skGer_deform F V (FreeAlgebra.ι F i) = Polynomial.C (FreeAlgebra.ι F i) * Polynomial.X := by
  change FreeAlgebra.lift F (skGer_deformGen F V) (FreeAlgebra.ι F i) = _
  exact FreeAlgebra.lift_ι_apply (skGer_deformGen F V) i

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_deform_ι

/-- The deformation on a constant.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_deform_freeConst (r : F) :
    skGer_deform F V (LVFreeAlgK2.freeConst F V r) =
      Polynomial.C (LVFreeAlgK2.freeConst F V r) := by
  change skGer_deformAlg F V (algebraMap F (FreeAlgebra F V) r) =
    Polynomial.C (algebraMap F (FreeAlgebra F V) r)
  exact ((skGer_deformAlg F V).commutes r).trans
    (Polynomial.algebraMap_apply (R := F) (A := FreeAlgebra F V) r)

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_deform_freeConst

/-- The augmentation kills generators.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_freeAug_ι (i : V) : LVFreeAlgK2.freeAug F V (FreeAlgebra.ι F i) = 0 := by
  change FreeAlgebra.lift F (0 : V → F) (FreeAlgebra.ι F i) = 0
  exact FreeAlgebra.lift_ι_apply (0 : V → F) i

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_freeAug_ι

/-- At `t = 0` the deformation is `const ∘ aug`, elementwise.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_constantCoeff_deform (a : FreeAlgebra F V) :
    Polynomial.constantCoeff (skGer_deform F V a) =
      LVFreeAlgK2.freeConst F V (LVFreeAlgK2.freeAug F V a) := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    change Polynomial.constantCoeff (skGer_deform F V (LVFreeAlgK2.freeConst F V r)) =
      LVFreeAlgK2.freeConst F V (LVFreeAlgK2.freeAug F V (LVFreeAlgK2.freeConst F V r))
    rw [skGer_deform_freeConst, LVFreeAlgK2.freeAug_freeConst, Polynomial.constantCoeff_apply]
    exact Polynomial.coeff_C_zero
  | grade1 i =>
    rw [skGer_deform_ι, skGer_freeAug_ι, map_zero (LVFreeAlgK2.freeConst F V),
      Polynomial.constantCoeff_apply]
    exact Polynomial.coeff_mul_X_zero _
  | mul a b ha hb =>
    rw [map_mul (skGer_deform F V), map_mul (Polynomial.constantCoeff (R := FreeAlgebra F V)),
      ha, hb, map_mul (LVFreeAlgK2.freeAug F V), map_mul (LVFreeAlgK2.freeConst F V)]
  | add a b ha hb =>
    rw [map_add (skGer_deform F V), map_add (Polynomial.constantCoeff (R := FreeAlgebra F V)),
      ha, hb, map_add (LVFreeAlgK2.freeAug F V), map_add (LVFreeAlgK2.freeConst F V)]

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_constantCoeff_deform

/-- At `t = 1` the deformation is the identity, elementwise.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_evalOne_deform (a : FreeAlgebra F V) :
    skGer_evalOne (FreeAlgebra F V) (skGer_deform F V a) = a := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    change skGer_evalOne (FreeAlgebra F V) (skGer_deform F V (LVFreeAlgK2.freeConst F V r)) =
      LVFreeAlgK2.freeConst F V r
    rw [skGer_deform_freeConst, skGer_evalOne_C]
  | grade1 i =>
    rw [skGer_deform_ι, map_mul (skGer_evalOne (FreeAlgebra F V)), skGer_evalOne_C,
      skGer_evalOne_X, mul_one]
  | mul a b ha hb =>
    rw [map_mul (skGer_deform F V), map_mul (skGer_evalOne (FreeAlgebra F V)), ha, hb]
  | add a b ha hb =>
    rw [map_add (skGer_deform F V), map_add (skGer_evalOne (FreeAlgebra F V)), ha, hb]

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne_deform

/-- `(t ↦ 0) ∘ ψ = const ∘ aug`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_constantCoeff_comp_deform :
    (Polynomial.constantCoeff (R := FreeAlgebra F V)).comp (skGer_deform F V) =
      (LVFreeAlgK2.freeConst F V).comp (LVFreeAlgK2.freeAug F V) :=
  RingHom.ext fun a => skGer_constantCoeff_deform F V a

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_constantCoeff_comp_deform

/-- `(t ↦ 1) ∘ ψ = id`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_evalOne_comp_deform :
    (skGer_evalOne (FreeAlgebra F V)).comp (skGer_deform F V) = RingHom.id (FreeAlgebra F V) :=
  RingHom.ext fun a => skGer_evalOne_deform F V a

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_evalOne_comp_deform

/-- Coefficientwise augmentation retracts coefficientwise constants on polynomial rings.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_mapFreeAug_comp_mapFreeConst :
    (Polynomial.mapRingHom (LVFreeAlgK2.freeAug F V)).comp
        (Polynomial.mapRingHom (LVFreeAlgK2.freeConst F V)) = RingHom.id (Polynomial F) := by
  refine RingHom.ext fun p => ?_
  rw [RingHom.comp_apply, RingHom.id_apply, Polynomial.coe_mapRingHom,
    Polynomial.coe_mapRingHom, Polynomial.map_map, LVFreeAlgK2.freeAug_comp_freeConst,
    Polynomial.map_id]

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_mapFreeAug_comp_mapFreeConst

/-- Constant coefficients commute with coefficientwise constants.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skGer_constantCoeff_comp_mapFreeConst :
    (Polynomial.constantCoeff (R := FreeAlgebra F V)).comp
        (Polynomial.mapRingHom (LVFreeAlgK2.freeConst F V)) =
      (LVFreeAlgK2.freeConst F V).comp (Polynomial.constantCoeff (R := F)) := by
  refine RingHom.ext fun p => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.constantCoeff_apply, Polynomial.constantCoeff_apply, Polynomial.coeff_map]

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_constantCoeff_comp_mapFreeConst

end Deform

end

end GroupApproximation.Full.LVFreeAlgGersten
