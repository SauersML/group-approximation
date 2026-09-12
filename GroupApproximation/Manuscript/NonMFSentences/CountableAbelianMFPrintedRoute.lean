import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.ResiduallyFiniteDimensionalMF
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.CDEOperatorMF
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import GroupApproximation.Meta.AxiomGuard

/-!
# A countable abelian group is MF, along the printed route

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1234–1237):

> A countable abelian group `A` is MF: `C*_max(A)` is commutative and separable, hence
> residually finite-dimensional and MF [BK], and Lemma `prop:mf-residual-calculus` applies.

`MFQuotientUnitsSentences.manuscriptSentence_countableAbelianIsMF` reaches the conclusion
by a different argument (LEF and residual finiteness of finitely generated abelian
groups).  This module carries the printed argument, step by step:

* `maximalGroupCStar_mul_comm`: `C*_max(A)` is commutative, because the canonical
  unitaries commute and their span is dense (`maximalGroupCStar_ext_of_generator`);
* separability is `maximalGroupCStar_separableSpace`;
* `isResiduallyFiniteDimensional`: a commutative C⋆-algebra is residually
  finite-dimensional, since its characters separate points (the Gelfand transform is
  isometric, `gelfandTransform_isometry`) and a character is a one-dimensional
  ⋆-representation;
* `isMFAlgebra`: a separable residually finite-dimensional C⋆-algebra is MF [BK]
  (`ResiduallyFiniteDimensionalMF.isMFAlgebra`, proved in the repository);
* `isOperatorMF`: Lemma `prop:mf-residual-calculus` (`isCDEOperatorMF_of_faithful_corona_map`)
  applied to the faithful canonical homomorphism `A → U(C*_max(A))`
  (`maximalGroupCStarUnitaryHom_injective`) and the faithful corona embedding of
  `C*_max(A)`.

Nothing is assumed.
-/

namespace GroupApproximation
namespace CountableAbelianMFPrintedRoute

open WeakDual

universe u

variable (A : Type u) [CommGroup A]

/-- The canonical generators multiply as the group does. -/
theorem generator_mul (g h : A) :
    maximalGroupCStarGenerator A g * maximalGroupCStarGenerator A h =
      maximalGroupCStarGenerator A (g * h) :=
  (congrArg (fun w : unitary (MaximalGroupCStar A) => (w : MaximalGroupCStar A))
    (map_mul (maximalGroupCStarUnitaryHom A) g h)).symm

/-- The canonical generators of an abelian group commute. -/
theorem generator_comm (g h : A) :
    maximalGroupCStarGenerator A g * maximalGroupCStarGenerator A h =
      maximalGroupCStarGenerator A h * maximalGroupCStarGenerator A g := by
  rw [generator_mul, generator_mul, mul_comm g h]

/-- **Printed: "`C*_max(A)` is commutative".**  Left and right multiplication by a
generator agree on the generators, hence everywhere by density of their span; then left
and right multiplication by an arbitrary element agree on the generators, hence
everywhere. -/
theorem maximalGroupCStar_mul_comm (x y : MaximalGroupCStar A) : x * y = y * x := by
  have hgen : ∀ (g : A) (z : MaximalGroupCStar A),
      maximalGroupCStarGenerator A g * z = z * maximalGroupCStarGenerator A g := by
    intro g z
    have hext := maximalGroupCStar_ext_of_generator A
      (f := ContinuousLinearMap.mul ℂ (MaximalGroupCStar A) (maximalGroupCStarGenerator A g))
      (h := (ContinuousLinearMap.mul ℂ (MaximalGroupCStar A)).flip
        (maximalGroupCStarGenerator A g))
      (fun k => by simpa using generator_comm A g k)
    simpa using congrArg (fun F => F z) hext
  have hext := maximalGroupCStar_ext_of_generator A
    (f := (ContinuousLinearMap.mul ℂ (MaximalGroupCStar A)).flip y)
    (h := ContinuousLinearMap.mul ℂ (MaximalGroupCStar A) y)
    (fun g => by simpa using hgen g y)
  simpa using congrArg (fun F => F x) hext

/-- The commutative C⋆-algebra structure on `C*_max(A)`, extending its C⋆-algebra
structure by `maximalGroupCStar_mul_comm`.  Not a global instance. -/
noncomputable abbrev commCStarAlgebra : CommCStarAlgebra (MaximalGroupCStar A) :=
  { (inferInstance : CStarAlgebra (MaximalGroupCStar A)) with
    mul_comm := maximalGroupCStar_mul_comm A }

/-- **Printed: "hence residually finite-dimensional".**  A nonzero element survives its
Gelfand transform, so some character does not vanish at it, and a character composed
with `ℂ = M_1(ℂ)` is a one-dimensional unital ⋆-representation. -/
theorem isResiduallyFiniteDimensional :
    IsResiduallyFiniteDimensional (MaximalGroupCStar A) := by
  letI : CommCStarAlgebra (MaximalGroupCStar A) := commCStarAlgebra A
  intro a ha
  have hne : gelfandTransform ℂ (MaximalGroupCStar A) a ≠ 0 := by
    intro h0
    apply ha
    apply (gelfandTransform_isometry (MaximalGroupCStar A)).injective
    exact h0.trans (map_zero (gelfandTransform ℂ (MaximalGroupCStar A))).symm
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.mp hne
  have hφa : φ a ≠ 0 := hφ
  refine ⟨1, (StarAlgHom.ofId ℂ (Matrix (Fin 1) (Fin 1) ℂ)).comp
    (StarAlgHomClass.toStarAlgHom φ), ?_⟩
  intro h0
  apply hφa
  apply (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ)).injective
  rw [map_zero]
  exact h0

/-- **Printed: "and MF [BK]".**  Separable and residually finite-dimensional, hence MF. -/
theorem isMFAlgebra [Countable A] : IsMFAlgebra (MaximalGroupCStar A) := by
  haveI := maximalGroupCStar_separableSpace A
  exact ResiduallyFiniteDimensionalMF.isMFAlgebra (MaximalGroupCStar A)
    (isResiduallyFiniteDimensional A)

/-- **Printed: "and Lemma `prop:mf-residual-calculus` applies".**  The faithful corona
embedding of `C*_max(A)` and the faithful canonical homomorphism `A → U(C*_max(A))` give
that `A` is MF. -/
theorem isOperatorMF [Countable A] : IsOperatorMF A := by
  obtain ⟨-, X, hne, hpos, -, e, he⟩ := isMFAlgebra A
  letI : ∀ n, Nonempty (X n) := hne
  exact (isCDEOperatorMF_iff_isOperatorMF A).mp
    (isCDEOperatorMF_of_faithful_corona_map X hpos e he
      (maximalGroupCStarUnitaryHom A) (maximalGroupCStarUnitaryHom_injective A))

/-- **Printed sentence (tex 1234–1237), every clause.**  For a countable abelian group
`A`: `C*_max(A)` is commutative and separable, residually finite-dimensional, and MF, and
`A` is MF. -/
def PrintedCountableAbelianIsMF : Prop :=
  ∀ (A : Type) [CommGroup A] [Countable A],
    (∀ x y : MaximalGroupCStar A, x * y = y * x) ∧
      TopologicalSpace.SeparableSpace (MaximalGroupCStar A) ∧
      IsResiduallyFiniteDimensional (MaximalGroupCStar A) ∧
      IsMFAlgebra (MaximalGroupCStar A) ∧
      IsOperatorMF A

theorem manuscriptSentence_countableAbelianIsMFPrintedRoute :
    PrintedCountableAbelianIsMF := by
  intro A _ _
  exact ⟨maximalGroupCStar_mul_comm A, maximalGroupCStar_separableSpace A,
    isResiduallyFiniteDimensional A, isMFAlgebra A, isOperatorMF A⟩

end CountableAbelianMFPrintedRoute
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.maximalGroupCStar_mul_comm
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isResiduallyFiniteDimensional
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isMFAlgebra
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isOperatorMF
#audit_closed_axioms GroupApproximation.CountableAbelianMFPrintedRoute.manuscriptSentence_countableAbelianIsMFPrintedRoute
