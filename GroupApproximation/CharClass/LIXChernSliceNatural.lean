import GroupApproximation.CharClass.LIXChernSlice

/-!
# `ChernSliceNatural` for `lixChern`, in the shape `hslice` asks for

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`cc-cohom-api`'s `hslice_of_props` consumes

```text
hnat : KnTwo.ChernSliceNatural (baseY dd) p5 p1
         (fun k => pull (Wu.lixIso dd).inv (2 * k) (g k)) v
```

with `g` the degreewise components of the class on `lixN`.  This file discharges
it for `g := lixChern dd P hcont hproj`.

**No bundle-level transport across `Wu.lixIso` is needed.**  The transported class
is restricted along `KnTwo.nSlice`, and `cc-cohom-api`'s `pull_nSlice_lixIso`
already says that this composite is restriction along `lixSlice`, the slice of
`lixN` itself.  So the two-step route -- transport the bundle to the other model,
then use the naturality proved there -- can be replaced by the one-step route:
`pull_lixChern_lixSlice` is stated at `lixSlice` and lands directly.

That also pins `v`: it is the degreewise Chern classes of the family restricted
along `lixSliceMap`, over `baseY dd`.  Whoever proves `ChernSliceValue` must prove
it of *that* `v`.

## Main declarations

* `chernSliceNatural_lixChern` — **`hnat`**, for a family of constant positive rank.

## Manuscript status

Machinery.  Discharges the first of the two hypotheses of the slice
identification of Lemma 2.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **`hnat`, discharged.**  For a family of constant positive rank on `N`, the
class transported to `KnTwo`'s model and restricted along `nSlice` is the class of
the family restricted along the slice of `lixN` itself.

The proof is `pull_nSlice_lixIso` composed with `pull_lixChern_lixSlice`: the
first identifies the two restrictions, the second is naturality at `lixN`.  The
bundle never crosses `Wu.lixIso`. -/
theorem chernSliceNatural_lixChern (dd : Fin ℓ → ℕ)
    (p5 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 5) (p1 : ↥sphereOne)
    (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s) :
    KnTwo.ChernSliceNatural (baseY dd) p5 p1
      (fun k => pull (Wu.lixIso dd).inv (2 * k) (lixChern dd P hcont hproj k))
      (LH.chernOf
        (comap (lixSliceMap dd p1 (unitVectorsThreeHomeoSphere.symm p5))
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd p1
          (unitVectorsThreeHomeoSphere.symm p5) y)) hs1) :=
  fun k =>
    (pull_nSlice_lixIso dd p1 p5 (2 * k) (lixChern dd P hcont hproj k)).trans
      (pull_lixChern_lixSlice dd p1 (unitVectorsThreeHomeoSphere.symm p5) P hcont
        hproj s hs1 hs k)

end

end CharClass
end GroupApproximation
