import GroupApproximation.CharClass.CohomologyLIXSliceBridge

/-!
# `hslice`, pre-staged over its two inputs

`WuStepDLix`'s `hslice` field is the identification of the pullback coefficient of
the Chern split with the coefficient of the slice polynomial.  `KnTwo`'s
`totalH_alpha_eq_sliceClass` proves it over two properties of the class and
nothing else; this file instantiates that at the geometric model, so that `hslice`
becomes one application once both properties are available.

The instantiation is definitional: `Wu.splitA` is by definition the pullback
coefficient placed in the ring, which is exactly what the bridge concludes about,
and `Wu.chernSplitOfGraded` is by definition the split of the transported family,
whose concentration hypothesis is `TotalH.map_of` applied to `hg`.

## Main declarations

* `hslice_of_props` — **`hslice` from `ChernSliceNatural` and `ChernSliceValue`**.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {ℓ : ℕ}

/-- **`hslice` from the two properties of the Chern class.**  Nothing else about
the class enters, and the two properties are the ones stated at `KnTwo`: the class
restricts along the slice to the class of the restricted family, and that class is
the slice polynomial. -/
theorem hslice_of_props (dd : Fin ℓ → ℕ) (p5 : Sphere 5) (p1 : Sphere 1)
    (γ : ℕ → TotalH (lixN dd)) (g : ∀ k : ℕ, Hmod2 (lixN dd) (2 * k))
    (hg : ∀ k : ℕ, γ k = TotalH.of (lixN dd) (2 * k) (g k))
    (v : ∀ k : ℕ, Hmod2 (KnTwo.YTop (baseY dd)) (2 * k))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hnat : KnTwo.ChernSliceNatural (baseY dd) p5 p1
      (fun k => pull (Wu.lixIso dd).inv (2 * k) (g k)) v)
    (hval : KnTwo.ChernSliceValue (baseY dd) v gen dd) :
    ∀ q : ℕ, Wu.splitA dd (Wu.chernSplitOfGraded dd γ g hg) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q :=
  fun q => KnTwo.totalH_alpha_eq_sliceClass (baseY dd) p5 p1
    (fun k => TotalH.map (Wu.lixIso dd).inv (γ k))
    (Wu.chernSplitOfGraded dd γ g hg)
    (fun k => pull (Wu.lixIso dd).inv (2 * k) (g k))
    (fun k => by rw [hg k, TotalH.map_of])
    v gen dd hnat hval q

end

end GroupApproximation.CharClass
