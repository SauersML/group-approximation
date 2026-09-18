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
