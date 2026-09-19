import GroupApproximation.CharClass.BundlePairs
import GroupApproximation.CharClass.ProjectiveSpaceInputs
import GroupApproximation.AlgTop.PuncturedNormedSphere

/-!
# The unit vectors of `ℂ^{d+1}` have the cohomology of `S^{2d+1}`

The Gysin datum for the tautological line needs the intersection of its two pieces
to be acyclic in the middle degrees.  The intersection retracts onto the sphere
bundle, and `cc-bundle`'s `sphereCpTautHomeo` identifies that with
`unitVectors (Fin (d+1))`, the vectors of Hermitian norm one.  So what is needed is
the cohomology of *that* model of the odd sphere.

`LemmaTwoStepCAbsEquiv` warns, at length and correctly, that identifying
`unitVectors (Fin 3)` with the vendored `Metric.sphere` in `EuclideanSpace ℝ (Fin 6)`
costs 153 lines, because `unitVectors` lives in a plain function type with its Pi
norm while `EuclideanSpace` is a `WithLp` structure.  Generalising that to every `d`
would be worse: the `fin_cases` that carries the `n = 3` proof does not exist for a
variable dimension.

None of it is necessary.  The route avoids the seam entirely by going through the
*punctured* space rather than the sphere:

* `cc-bundle`'s `prodPuncturedHomotopyEquivSphere`, at the trivial bundle over a
  point, retracts `ℂ^{d+1} ∖ 0` onto `unitVectors (Fin (d+1))`.  This is a radial
  retraction inside one function type, with no norm identity anywhere.
* `AlgTop.complexPuncturedHomotopyEquivSphere` already relates `ℂ^{d+1} ∖ 0` to the
  vendored sphere, and it crosses the `WithLp` seam through a *linear* equivalence,
  which only has to preserve being nonzero, not the norm.

Composing them is five lines.  The moral is the one the lane keeps relearning: the
expensive object was the isometry, and nothing in the argument ever wanted one.

## Main declarations

* `puncturedHomotopyEquivUnitVectors` — the radial retraction, with no bundle.
* `unitVectorsHomotopyEquivSphere` — the unit vectors are the odd sphere.
* `hasSphereCohomology_unitVectors` — **and so is their cohomology**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-- **The punctured space retracts onto the unit vectors**, with no bundle in
sight: `cc-bundle`'s retraction at the trivial bundle over a point, with the
point divided out on both sides. -/
def puncturedHomotopyEquivUnitVectors (ι : Type) [Fintype ι] [DecidableEq ι] :
    ContinuousMap.HomotopyEquiv ↥({v : ι → ℂ | v ≠ 0}) ↥(unitVectors ι) :=
  ((Homeomorph.punitProd ↥({v : ι → ℂ | v ≠ 0})).symm.toHomotopyEquiv.trans
      (Bundle.prodPuncturedHomotopyEquivSphere (X := PUnit) (ι := ι))).trans
    (Homeomorph.punitProd ↥(unitVectors ι)).toHomotopyEquiv

/-- **The unit vectors of `ℂ^{d+1}` are the odd sphere**, homotopy equivalently.
Through the punctured space, so the `WithLp` seam is crossed by a linear
equivalence that need only preserve being nonzero. -/
def unitVectorsHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(unitVectors (Fin (d + 1)))
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1) :=
  (puncturedHomotopyEquivUnitVectors (Fin (d + 1))).symm.trans
    (AlgTop.complexPuncturedHomotopyEquivSphere d)

/-- **The unit vectors have the cohomology of `S^{2d+1}`.** -/
theorem hasSphereCohomology_unitVectors (d : ℕ) :
    HasSphereCohomology (TopCat.of ↥(unitVectors (Fin (d + 1)))) (2 * d + 1) := by
  refine HasSphereCohomology.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquiv (unitVectorsHomotopyEquivSphere d) k).symm) ?_
  exact hasSphereCohomology_sphere (2 * d + 1) (by omega)

/-- **The unit vectors are acyclic below the top**, which is the form the Gysin
datum's pair condition consumes. -/
theorem eq_zero_unitVectors (d k : ℕ) (hk0 : k ≠ 0) (hk : k ≠ 2 * d + 1)
    (a : Hmod2 (TopCat.of ↥(unitVectors (Fin (d + 1)))) k) : a = 0 :=
  (hasSphereCohomology_unitVectors d).2.2 k hk0 hk a

end

end Gysin
end CharClass
end GroupApproximation
