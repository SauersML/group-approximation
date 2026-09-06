import GroupApproximation.CharClass.CohomologyLIXHslice
import GroupApproximation.CharClass.LIXChernSlice

/-!
# `hslice` over one hypothesis

`cc-projective` proved naturality directly at `lixN`, against the slice of the
geometric model rather than after transporting the bundle.  Composed with the
identification of the two slices, that discharges `ChernSliceNatural` for the
mod-2 Chern classes, and `hslice` is left over `ChernSliceValue` alone.

Worth recording why this route exists.  The obvious one is to transport the bundle
across the model isomorphism and quote naturality on the other side, and that needs
an identification of Chern classes across the models which nothing supplies.
Proving naturality on the model the classes already live on avoids it entirely:
only the *slice* has to cross, and that crossing is `rfl`.

## Main declarations

* `chernSliceNatural_lixChern` — **`ChernSliceNatural` discharged** for the
  degreewise Chern classes of a family of constant positive rank.
* `hslice_of_chernSliceValue` — hence `hslice` over `ChernSliceValue` alone.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {ℓ : ℕ}

/-- **`ChernSliceNatural` for the degreewise Chern classes.**  The class restricted
along the slice of the mapping-torus base is the class of the restricted family.
Only the slice crosses the two models, and that crossing is definitional. -/
theorem chernSliceNatural_lixChern (dd : Fin ℓ → ℕ) (p5 : Sphere 5) (p1 : ↥sphereOne)
    (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s) :
    KnTwo.ChernSliceNatural (baseY dd) p5 p1
      (fun k => pull (Wu.lixIso dd).inv (2 * k) (lixChern dd P hcont hproj k))
      (fun k => LH.chernOf
        (Bundle.comap (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5))
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5) y))
        hs1 k) := by
  intro k
  rw [pull_nSlice_lixIso]
  exact pull_lixChern_lixSlice dd p1 (unitVectorsThreeHomeoSphere.symm p5)
    P hcont hproj s hs1 hs k

/-- **`hslice` over `ChernSliceValue` alone.**  The naturality half is discharged,
so the only property of the Chern class still asked for is its value on the
restricted family. -/
theorem hslice_of_chernSliceValue (dd : Fin ℓ → ℕ) (p5 : Sphere 5) (p1 : ↥sphereOne)
    (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s)
    (γ : ℕ → TotalH (lixN dd))
    (hg : ∀ k : ℕ, γ k = TotalH.of (lixN dd) (2 * k) (lixChern dd P hcont hproj k))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hval : KnTwo.ChernSliceValue (baseY dd)
      (fun k => LH.chernOf
        (Bundle.comap (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5))
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5) y))
        hs1 k) gen dd) :
    ∀ q : ℕ, Wu.splitA dd
        (Wu.chernSplitOfGraded dd γ (fun k => lixChern dd P hcont hproj k) hg) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q :=
  hslice_of_props dd p5 p1 γ (fun k => lixChern dd P hcont hproj k) hg _ gen
    (chernSliceNatural_lixChern dd p5 p1 P hcont hproj s hs1 hs) hval

end

end GroupApproximation.CharClass
