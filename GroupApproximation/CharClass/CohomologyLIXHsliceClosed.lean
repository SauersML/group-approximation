import GroupApproximation.CharClass.CohomologyLIXHslice
import GroupApproximation.CharClass.LIXChernSliceNatural

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

* `hslice_of_chernSliceValue` — **`hslice` over `ChernSliceValue` alone**, over
  `cc-projective`'s `chernSliceNatural_lixChern` for the naturality half.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {ℓ : ℕ}

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
      (LH.chernOf
        (Bundle.comap (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5))
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5) y))
        hs1) gen dd) :
    ∀ q : ℕ, Wu.splitA dd
        (Wu.chernSplitOfGraded dd γ (fun k => lixChern dd P hcont hproj k) hg) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q :=
  hslice_of_props dd p5 p1 γ (fun k => lixChern dd P hcont hproj k) hg _ gen
    (chernSliceNatural_lixChern dd p5 p1 P hcont hproj s hs1 hs) hval

end

end GroupApproximation.CharClass
