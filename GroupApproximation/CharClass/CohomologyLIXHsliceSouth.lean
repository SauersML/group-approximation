import GroupApproximation.CharClass.CohomologyLIXHsliceClosed

/-!
# `hslice` at the south pole

`hslice_of_chernSliceValue` quantifies over both marked points, which is correct
but misleading about what an assembly can do with it.  The slice equation
`cc-lix-odd` proved holds only at the two poles: away from them the clutching
field is present and the identification of the restricted mapping torus fails.
So although the circle point is free in the statement, it is **not** free in
practice.

This file pins it, so nobody assembling has to rediscover the constraint.  The
general form is untouched; this is a specialisation, not a replacement.

`cc-steenrod` raised this after reading the index type of the restricted family
rather than its description, which is also how the doubled index in that seam was
found.

## Main declarations

* `hslice_of_chernSliceValue_south` — `hslice` at `southPole`, the point
  `cc-lix-odd`'s `lixZero` uses.
-/

open CategoryTheory
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

noncomputable section

variable {ℓ : ℕ}

/-- **`hslice` at the south pole.**  The sphere coordinate stays free, since the
slice equation quantifies over the whole base point; only the circle coordinate is
constrained, and of the two poles this is the one `lixZero` takes. -/
theorem hslice_of_chernSliceValue_south (dd : Fin ℓ → ℕ)
    (p5 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 5)
    (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s)
    (γ : ℕ → TotalH (lixN dd))
    (hg : ∀ k : ℕ, γ k = TotalH.of (lixN dd) (2 * k) (lixChern dd P hcont hproj k))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hval : KnTwo.ChernSliceValue (baseY dd)
      (LH.chernOf
        (Bundle.comap (lixSliceMap dd _root_.GroupApproximation.CharClass.southPole
            (unitVectorsThreeHomeoSphere.symm p5))
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd _root_.GroupApproximation.CharClass.southPole
          (unitVectorsThreeHomeoSphere.symm p5) y)) hs1) gen dd) :
    ∀ q : ℕ, Wu.splitA dd
        (Wu.chernSplitOfGraded dd γ (fun k => lixChern dd P hcont hproj k) hg) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q :=
  hslice_of_chernSliceValue dd p5 _root_.GroupApproximation.CharClass.southPole
    P hcont hproj s hs1 hs γ hg gen hval

end

end GroupApproximation.CharClass
