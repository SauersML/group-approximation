import GroupApproximation.CharClass.ThomKunnethProjective
import GroupApproximation.CharClass.ThomToolkitInstance
import GroupApproximation.CharClass.ThomPuncturedPi
import GroupApproximation.CharClass.EulerLocalChart
import GroupApproximation.CharClass.ProjectiveSpaceComputation
import GroupApproximation.CharClass.ProjectiveSpaceHomogeneous

/-!
# Complex projective space, punctured at an arbitrary point

`cc-lix-odd`'s `puncturedAcyclic_lixBase` takes three projective facts as explicit
hypotheses.  Two of them are compositions of cc-thom's own results with
`cc-projective`'s green homogeneity and puncture retraction, and are discharged here:

* `puncturedAcyclic_CP` — `ℂP^d` is top-punctured acyclic at *every* point, not just the
  base point.  Homogeneity moves an arbitrary point to the base point
  (`exists_homeomorph_mapsTo_basePoint`), `PuncturedAcyclic.congr'` transports, and the
  base-point case is `punctOpenHomotopyEquiv` through
  `puncturedAcyclic_of_homotopyEquiv`.
* `kunnethFactor_CP_punctured` — the complement of a point in `ℂP^d` is a Künneth
  factor, by the same transport applied to `kunnethFactor_CP`.

The vanishing input is `cc-projective`'s unconditional `hasCPCohomology_CP`, repackaged
here as `isZero_cohomology_CP`.

## Main results

* `isZero_cohomology_CP`, `KunnethFactor.congrHomotopy`,
  `puncturedAcyclic_CP`, `kunnethFactor_CP_punctured`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

noncomputable section

/-- `H^k(ℂP^d; F₂)` vanishes above `2d`, from `cc-projective`'s unconditional
`hasCPCohomology_CP`. -/
theorem isZero_cohomology_CP (d k : ℕ) (hk : 2 * d < k) :
    IsZero (cohomologyZMod2 (TopCat.of (CP d)) k) := by
  have h := (hasCPCohomology_CP d).2 k (fun n hn => by omega)
  haveI : Subsingleton (Hmod2 (CPtop d) k) := ⟨fun a c => by rw [h a, h c]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **Being a Künneth factor transports along a homotopy equivalence.** -/
theorem KunnethFactor.congrHomotopy {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W]
    {q : ℕ} (e : ContinuousMap.HomotopyEquiv Y W) (h : KunnethFactor W q) :
    KunnethFactor Y q :=
  ⟨fun A _ p hA k hk => thomIsZero_of_linearEquiv
    (pullEquivOfHomotopyEquiv ((ContinuousMap.HomotopyEquiv.refl A).prodCongr e) k).symm
    (h.prod A p hA k hk)⟩

/-- **`ℂP^d` is top-punctured acyclic at every point.** -/
theorem puncturedAcyclic_CP :
    ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w := by
  rintro (_ | d) hd w
  · omega
  · obtain ⟨e, he⟩ := exists_homeomorph_mapsTo_basePoint (d + 1) w
    refine PuncturedAcyclic.congr' cohomologyToolkit e he ?_
    refine puncturedAcyclic_of_homotopyEquiv cohomologyToolkit (by omega)
      (fun k hk => isZero_cohomology_CP (d + 1) k hk) ?_
      (fun k hk => isZero_cohomology_CP d k hk) (by omega)
    exact punctOpenHomotopyEquiv d

/-- **The complement of a point in `ℂP^d` is a Künneth factor.** -/
theorem kunnethFactor_CP_punctured :
    ∀ d : ℕ, 0 < d → ∀ w : CP d, KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1) := by
  rintro (_ | d) hd w
  · omega
  · obtain ⟨e, he⟩ := exists_homeomorph_mapsTo_basePoint (d + 1) w
    have hset : ({e w}ᶜ : Set (CP (d + 1))) = ({basePoint (d + 1)}ᶜ : Set (CP (d + 1))) := by
      rw [he]
    refine KunnethFactor.congrHomotopy
      (((homeomorphCompl e w).trans (Homeomorph.setCongr hset)).toHomotopyEquiv.trans
        (punctOpenHomotopyEquiv d)) ?_
    exact (kunnethFactor_CP d).mono (by omega)

end

end GroupApproximation.CharClass
