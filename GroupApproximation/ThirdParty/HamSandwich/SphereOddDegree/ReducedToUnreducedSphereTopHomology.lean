import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereTopHomologyReduction
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian

































































open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## The one-point space and the augmentation map -/

/-- The unique continuous map from a space `X` to the one-point space `PUnit`.
It induces the augmentation on homology. -/
def toPUnit (X : TopCat.{0}) : X ⟶ TopCat.of (PUnit : Type) :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- **Reduced integral singular homology** of a space `X`, defined as the kernel of
the augmentation `Hₙ(X; ℤ) → Hₙ(pt; ℤ)` induced by the unique map `X → pt`. -/
def reducedSingularHomologyℤ (n : ℕ) (X : TopCat.{0}) : ModuleCat.{0} ℤ :=
  kernel ((singularHomologyℤ n).map (toPUnit X))

/-! ## Vanishing of point homology in positive degree -/

/-- `Hₙ(pt; ℤ) = 0` for `n ≥ 1`: the one-point space is totally disconnected, so
its higher singular homology vanishes. -/
theorem isZero_singularHomologyℤ_punit_of_pos (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((singularHomologyℤ n).obj (TopCat.of (PUnit : Type))) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (PUnit : Type)) (by omega)

/-! ## The reduced-to-unreduced bridge -/

/-- **Bridge, general form.** Whenever the point's `n`-th homology vanishes, reduced
and unreduced `n`-th homology of `X` agree.  The augmentation `Hₙ(X) → Hₙ(pt)` is
then the zero map, whose kernel is all of `Hₙ(X)`. -/
def reducedToUnreducedIsoOfIsZero (n : ℕ) (X : TopCat.{0})
    (hpt : IsZero ((singularHomologyℤ n).obj (TopCat.of (PUnit : Type)))) :
    reducedSingularHomologyℤ n X ≅ (singularHomologyℤ n).obj X :=
  kernelIsoOfEq (hpt.eq_of_tgt _ 0) ≪≫ kernelZeroIsoSource

/-- **Reduced-to-unreduced bridge.** For `n ≥ 1`, reduced and unreduced integral
singular homology agree: `H̃ₙ(X; ℤ) ≅ Hₙ(X; ℤ)`. -/
def reducedToUnreducedIso (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) :
    reducedSingularHomologyℤ n X ≅ (singularHomologyℤ n).obj X :=
  reducedToUnreducedIsoOfIsZero n X (isZero_singularHomologyℤ_punit_of_pos n hn)

/-! ## Consequence for the sphere top-homology family -/

/-- Transport a reduced sphere top-homology identification `H̃ₙ(Sⁿ; ℤ) ≅ ℤ`
(`n ≥ 1`) across the bridge to the ordinary identification `Hₙ(Sⁿ; ℤ) ≅ ℤ`
required by the degree API. -/
def sphereTopHomologyIso_of_reduced {n : ℕ} (hn : 1 ≤ n)
    (e : reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  (reducedToUnreducedIso n hn (TopCat.sphere.{0} n)).symm ≪≫ e

/-- **Reduced ⇒ ordinary, for the whole positive family.** A reduced sphere
top-homology computation in every dimension `n ≥ 1` yields the ordinary
top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension `n ≥ 1`. -/
def sphereTopHomologyIsoPos_of_reducedSphereHomology
    (red : ∀ n : ℕ, 1 ≤ n →
      (reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)) :
    ∀ n : ℕ, 1 ≤ n → SphereTopHomologyIso n :=
  fun n hn => sphereTopHomologyIso_of_reduced hn (red n hn)

/-- A reduced sphere top-homology computation yields a genuine (non-vacuous)
positive sphere orientation, hence the unconditional positive-degree theory. -/
def sphereOrientationPos_of_reducedSphereHomology
    (red : ∀ n : ℕ, 1 ≤ n →
      (reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)) :
    SphereOrientationPos :=
  ⟨sphereTopHomologyIsoPos_of_reducedSphereHomology red⟩

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

