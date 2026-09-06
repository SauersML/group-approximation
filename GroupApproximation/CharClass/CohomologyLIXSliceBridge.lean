import GroupApproximation.CharClass.CohomologyParitySlice
import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv

/-!
# The slice, across the two models

`ChernSliceNatural` is stated at `KnTwo.NTop Y = (Y × S⁵) × S¹`, with the slice
`nSlice`.  The Chern classes live at `lixN dd = S¹ × (S⁵ × Y)`, and the two models
are related by `Wu.lixIso`.  This file is the identification of the two slices, so
that a naturality statement proved at `lixN` lands in the shape the `Prop` asks
for.

The identification is pointwise: `nSlice` sends `y` to `((y, p₅), p₁)`, the inverse
model homeomorphism sends that to `(p₁, (φ⁻¹ p₅, y))`, and that is the `lixN` slice
at those points.  So the whole content is one `ext`, and the only care needed is
which of `Sphere 5` and `unitVectors (Fin 3)` each point lives in.

The circle needs no translation at all: `Wu.circHomeo` is `Homeomorph.refl`, since
`Fin (1 + 1)` reduces to `Fin 2`, so `sphereOne` and `Sphere 1` are the same type.

## Main declarations

* `lixSlice` — the slice of `lixN dd` at a pair of marked points.
* `nSlice_comp_lixIso_inv` — **the identification of the two slices**.
* `pull_nSlice_lixIso` — hence the identification of the two restrictions, which
  is what `ChernSliceNatural` consumes.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {ℓ : ℕ}

/-- **The slice of `lixN`** at a point of the circle and a point of the sphere of
unit vectors: `y ↦ (p₁, (q₅, y))`. -/
def lixSlice (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne) (q5 : ↥(unitVectors (Fin 3))) :
    KnTwo.YTop (baseY dd) ⟶ lixN dd :=
  cmap ⟨fun y => (p1, (q5, y)),
    continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

/-- **The two slices agree across the model homeomorphism.**  Both maps are
explicit, so this is pointwise. -/
theorem nSlice_comp_lixIso_inv (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne) (p5 : Sphere 5) :
    KnTwo.nSlice (baseY dd) p5 p1 ≫ (Wu.lixIso dd).inv
      = lixSlice dd p1 (unitVectorsThreeHomeoSphere.symm p5) := by
  apply TopCat.Hom.ext
  ext y
  rfl

/-- **Hence the two restrictions agree.**  Restricting a class of `lixN` along its
own slice is the same as transporting it to the other model and restricting along
`nSlice`, which is the form `ChernSliceNatural` is stated in. -/
theorem pull_nSlice_lixIso (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne) (p5 : Sphere 5)
    (k : ℕ) (z : Hmod2 (lixN dd) k) :
    pull (KnTwo.nSlice (baseY dd) p5 p1) k (pull (Wu.lixIso dd).inv k z)
      = pull (lixSlice dd p1 (unitVectorsThreeHomeoSphere.symm p5)) k z := by
  rw [← pull_comp, nSlice_comp_lixIso_inv]

end

end GroupApproximation.CharClass
