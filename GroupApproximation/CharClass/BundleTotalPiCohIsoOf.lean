import GroupApproximation.CharClass.BundleTotalPiCohIso
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The bundle projection is an isomorphism on `K`-cohomology

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`BundleTotalPiCohIso` gives at `F₂` that `π^* : H^n(X) → H^n(Total p)` is a linear
isomorphism, through the zero-section deformation retraction.  The retraction is topology and
homotopy invariance over any commutative ring is `pullEquivOfHomotopyEquivOf`.

## Main declarations

* `Bundle.totalPiCohIsoOf`, `Bundle.bijective_totalPiPullOf`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace Bundle

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **The bundle projection is a linear isomorphism on `H^n(−; K)`**, through the zero-section
deformation retraction. -/
noncomputable def totalPiCohIsoOf (K : Type) [CommRing K] (p : Bundle X ι) (n : ℕ) :
    Hmod K (TopCat.of X) n ≃ₗ[K] Hmod K (TopCat.of (Total p)) n :=
  pullEquivOfHomotopyEquivOf K (totalHomotopyEquivBase p) n

/-- **`π^*` is bijective on `K`-cohomology.** -/
theorem bijective_totalPiPullOf (K : Type) [CommRing K] (p : Bundle X ι) (n : ℕ) :
    Function.Bijective (pull (K := K) (cmap (totalPi p)) n) :=
  (totalPiCohIsoOf K p n).bijective

#audit_axioms bijective_totalPiPullOf

end Bundle

end GroupApproximation.CharClass
