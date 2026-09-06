import GroupApproximation.CharClass.MayerVietorisVanishing
import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.ThomKunnethSphere

/-!
# The cohomology toolkit, instantiated

`ThomPuncturedRecursion.CohomologyToolkit` bundles the four facts about mod-2 singular
cohomology that the punctured-product recursion consumes.  Each was a `NEEDS` item when
the recursion was written; all four are now theorems, so the structure is a term rather
than a hypothesis and every result of the recursion is unconditional in it.

* the Mayer–Vietoris vanishing form is `MayerVietorisVanishing.isZero_cohomology_of_cover'`,
  cc-thom's own, built on `cc-cohom-api`'s dualized sequence;
* homeomorphism and homotopy-equivalence invariance are `cc-cohom-api`'s
  `pullEquivOfHomeomorph` and `pullEquivOfHomotopyEquiv`, transported by
  `thomIsZero_of_linearEquiv`;
* the contractible case is `cc-cohom-api`'s `cohomology_isZero_of_contractible`.

The Künneth input is deliberately *not* a field of the toolkit — fully general Künneth
is unreachable here — and is supplied per factor as `KunnethFactor`; see
`ThomKunnethSphere.lean` for the sphere and contractible instances.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The cohomology toolkit of the punctured-product recursion, as a term.** -/
theorem cohomologyToolkit : CohomologyToolkit :=
  ⟨fun Z _ U V hUV m hI hU hV => isZero_cohomology_of_cover' Z U V hUV m hI hU hV,
   fun _ _ _ _ e n h => thomIsZero_of_linearEquiv (pullEquivOfHomeomorph e n).symm h,
   fun _ _ _ _ e n h => thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquiv e n).symm h,
   fun A _ hc n hn => by
     haveI := hc
     exact cohomology_isZero_of_contractible A n hn⟩

/-- The punctured-product recursion, with the toolkit discharged. -/
theorem puncturedAcyclic_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y] {dX dY : ℕ} {x₀ : X} {y₀ : Y}
    (kY : KunnethFactor Y dY) (kY' : KunnethFactor ↥({y₀}ᶜ : Set Y) (dY - 1))
    (hX : PuncturedAcyclic X dX x₀) (hY : PuncturedAcyclic Y dY y₀) :
    PuncturedAcyclic (X × Y) (dX + dY) (x₀, y₀) :=
  PuncturedAcyclic.prod cohomologyToolkit kY kY' hX hY

/-- The sphere base case, with the toolkit discharged. -/
theorem puncturedAcyclic_sphere' {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (v : Metric.sphere (0 : E) 1)
    (hvanish : ∀ k, n < k →
      IsZero (cohomologyZMod2 (TopCat.of ↥(Metric.sphere (0 : E) 1)) k)) :
    PuncturedAcyclic ↥(Metric.sphere (0 : E) 1) n v :=
  puncturedAcyclic_sphere cohomologyToolkit hn v hvanish

end GroupApproximation.CharClass
