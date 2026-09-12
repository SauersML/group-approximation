import GroupApproximation.CharClass.MayerVietorisElement
import GroupApproximation.CharClass.ThomPuncturedRecursion

/-!
# Mayer–Vietoris in vanishing form, and the punctured-product recursion's toolkit field

The punctured-product recursion of `CharClass/ThomPuncturedRecursion.lean` uses exactly
one consequence of Mayer–Vietoris: if the intersection has no cohomology in degree `m`
and the two pieces have none in degree `m + 1`, then neither does the ambient space.
This is immediate from `mvExactX` plus the vanishing of the intersection, since the
connecting map's source is then zero.

`isZero_cohomology_of_cover'` is the same statement over a plain type with
`U V : Opens Z`, which is the shape of the `mv` field of `CohomologyToolkit`; it
discharges need (A1) of `notes/lix-lane-reports/cc-thom.md`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **Mayer–Vietoris, vanishing form.**  A class of `H^{m+1}(X)` restricting to zero on
both pieces comes from `H^m(U ∩ V)`, which is zero. -/
theorem isZero_cohomology_of_cover (U V : Opens X) (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (Hmod2 (mvInter U V) m))
    (hU : IsZero (Hmod2 (mvU U) (m + 1)))
    (hV : IsZero (Hmod2 (mvU V) (m + 1))) :
    IsZero (Hmod2 X (m + 1)) := by
  haveI := ModuleCat.subsingleton_of_isZero hI
  haveI := ModuleCat.subsingleton_of_isZero hU
  haveI := ModuleCat.subsingleton_of_isZero hV
  have hsub : ∀ z : Hmod2 X (m + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (mvExactX U V hUV m z).1
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  haveI : Subsingleton (Hmod2 X (m + 1)) := ⟨fun a b => by rw [hsub a, hsub b]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The same over a plain topological space: the `mv` field of `CohomologyToolkit`,
i.e. need (A1) of the cc-thom report. -/
theorem isZero_cohomology_of_cover' (Z : Type) [TopologicalSpace Z] (U V : Opens Z)
    (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (cohomologyZMod2 (TopCat.of ↥(U ⊓ V)) m))
    (hU : IsZero (cohomologyZMod2 (TopCat.of ↥U) (m + 1)))
    (hV : IsZero (cohomologyZMod2 (TopCat.of ↥V) (m + 1))) :
    IsZero (cohomologyZMod2 (TopCat.of Z) (m + 1)) :=
  isZero_cohomology_of_cover (X := TopCat.of Z) U V hUV m hI hU hV

end

end GroupApproximation.CharClass
