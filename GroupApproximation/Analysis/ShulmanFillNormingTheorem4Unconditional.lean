import GroupApproximation.Analysis.ShulmanFillNormingTheorem4Refuted
import GroupApproximation.Analysis.ShulmanFillNormingPrintedPairRefuted
import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Analysis.CuntzPedersenJordanMatrixTest
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The model-first form of Theorem 4 is refuted unconditionally

`ShulmanFillNormingTheorem4Refuted.not_theorem4ModelFirst` refutes
`Theorem4ModelFirstStatement` **conditionally**: it consumes a separable MF
algebra `B` carrying a faithful representation and a non-commuting pair, and
leaves the reader to supply one.  Every ingredient has been on `origin/main`
for some time, in three different files, so the refutation read as an open
hypothesis while being a closed theorem waiting to be assembled.

This file supplies `M₂(ℂ)` and closes it:

* `IsMFAlgebra M₂(ℂ)` from `isMFAlgebra_cstarMatrix` at `isMFAlgebra_complex`;
* separability as an instance off `IsMFAlgebra.1` — `IsMFAlgebra` is the
  conjunction `SeparableSpace ∧ HasMFEmbedding`, so the instance the ambient
  binder demands is the first projection and needs no separate argument;
* the faithful representation as the composite star algebra **equivalence**
  `CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM`, whose
  injectivity is then free;
* the non-commuting pair from `CuntzPedersenJordanMatrixTest.exists_not_commute`,
  the matrix units `e₀₁` and `e₁₀`.

## The one point of friction

`CStarMatrix` is a type synonym for `Matrix` carrying its own algebraic
instances, and across such a synonym `rw` and instance search do not pass while
`exact` does.  The representation is therefore built by *composing bundled
equivalences* rather than by rewriting a matrix map into an operator map:
`ofMatrixStarAlgEquiv` is the bundled form of `ofMatrix` (which is
`Equiv.refl`), and `toEuclideanCLM` is Mathlib's star algebra equivalence
between square matrices and endomorphisms of Euclidean space.  Going through
the bundled maps keeps every step at `exact`.
-/

namespace GroupApproximation
namespace ShulmanFill

open CuntzPedersenJordanMatrixTest

/-- `M₂(ℂ)` is MF: it is a matrix amplification of `ℂ`, which is. -/
theorem isMFAlgebra_m2 : IsMFAlgebra M2 :=
  MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix 2 isMFAlgebra_complex

/-- **The faithful representation of `M₂(ℂ)` on `ℂ²`.**  Composed from bundled
equivalences so that no step has to cross the `CStarMatrix` type synonym by
rewriting. -/
noncomputable def m2Rep :
    M2 ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2) (A := ℂ)).symm.trans
    Matrix.toEuclideanCLM

/-- **The model-first statement is false, with no hypotheses.**

`not_theorem4ModelFirst` is the conditional refutation; this is it evaluated at
`M₂(ℂ)`.  Nothing new is proved about Shulman's Theorem 4 — the mathematics is
entirely in `commute_of_theorem4ModelFirst`, which shows the recorded binder
forces every separable MF algebra with a faithful representation to be
commutative.  What changes is the *status* of the row: a conditional refutation
still reads as an assumption at a glance, and an unconditional one cannot. -/
theorem not_theorem4ModelFirst_unconditional : ¬ Theorem4ModelFirstStatement := by
  obtain ⟨a, b, hab⟩ := exists_not_commute
  haveI : TopologicalSpace.SeparableSpace M2 := isMFAlgebra_m2.1
  exact not_theorem4ModelFirst isMFAlgebra_m2 m2Rep.toStarAlgHom
    m2Rep.injective hab

end ShulmanFill
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanFill.not_theorem4ModelFirst_unconditional
#audit_axioms GroupApproximation.ShulmanFill.isMFAlgebra_m2
