import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.LemmaTwoStepC
import GroupApproximation.CharClass.BundleSpace
import GroupApproximation.CharClass.RelativeFunctorial
import GroupApproximation.CharClass.CohomologyBridge

/-!
# The pair `(E, E ∖ 0)` at the real base, and the section as a map of pairs

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C), items 1 and 2 of the final
instantiation.

`CharClass/LIXBundleModel.lean` made the mapping torus a `Bundle`.  This file forms the
pair its Thom class lives on and produces the morphism `cc-thom`'s residual is about.

## The two facts that make the section a map of pairs

Both were already proved in this lane, and each is exactly one of the two conjuncts of
`Bundle.puncturedSet`:

* `lixSection_mem` says `W_g *ᵥ σ = σ`, which is membership in `Bundle.totalSet`;
* `lixSection_eq_zero_iff` says `σ` vanishes only at `lixZero`, which off that point is
  the second conjunct `v.2 ≠ 0`.

So the section lands in the total space, and carries the punctured base into the punctured
total space, with no further geometry.

## `sRel`

`cc-relative`'s `relPullback` is contravariant and its map-of-pairs hypothesis is literally
`∀ x ∈ A, f x ∈ B`, with no bundled morphism type to build.  Applying it to the section
gives

```text
H^n(E, E ∖ 0) ⟶ H^n(lixN, lixN ∖ {lixZero}),
```

which is the direction that pulls the Euler class back, and is `cc-thom`'s `sRel`.

## Main results

* `lixTotalPair`, `lixPuncturedInTotal` — the pair, as a `TopCat` object and a subset.
* `lixSectionTotal` — the section into the total space.
* `lixSectionTotal_mapsTo` — it is a map of pairs.
* `lixSRel` — **the morphism `cc-thom`'s residual is about**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The pair -/

/-- The total space of the mapping torus, as a `TopCat` object. -/
def lixTotalPair (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.{0} :=
  TopCat.of (Bundle.Total (lixBundle G hGc hGu))

/-- The complement of the zero section, as a subset of the total space. -/
def lixPuncturedInTotal (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Set (Bundle.Total (lixBundle G hGc hGu)) :=
  (Subtype.val : Bundle.Total (lixBundle G hGc hGu) → _) ⁻¹'
    Bundle.puncturedSet (lixBundle G hGc hGu)

/-! ## 2. The section into the total space -/

/-- **The section, into the total space of the bundle.**  Membership is `lixSection_mem`,
which is `Bundle.totalSet` on the nose. -/
def lixSectionTotal (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    C(↥sphereOne × baseM dd, Bundle.Total (lixBundle G hGc hGu)) where
  toFun x := ⟨(x, lixSection G x), lixSection_mem hGu x⟩
  continuous_toFun :=
    (continuous_id.prodMk (lixSection_continuous hGc hGu hGe)).subtype_mk _

@[simp] theorem lixSectionTotal_coe (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)
    (x : ↥sphereOne × baseM dd) :
    ((lixSectionTotal hGc hGu hGe x : Bundle.Total (lixBundle G hGc hGu)) :
      (↥sphereOne × baseM dd) × (VIdx dd ⊕ VIdx dd → ℂ)) = (x, lixSection G x) := rfl

/-! ## 3. It is a map of pairs -/

/-- **The section carries the punctured base into the punctured total space.**  Away from
its single zero the section is nonzero, which is the second conjunct of
`Bundle.puncturedSet`; the first is `lixSection_mem`. -/
theorem lixSectionTotal_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    ∀ x ∈ ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)),
      (ConcreteCategory.hom (cmap (lixSectionTotal hGc hGu hGe))) x ∈
        lixPuncturedInTotal hGc hGu := by
  intro x hx
  refine ⟨lixSection_mem hGu x, ?_⟩
  intro hzero
  exact hx (by
    have := (lixSection_eq_zero_iff hGe x).mp hzero
    simpa [lixZero] using this)

/-! ## 4. `sRel` -/

/-- **The morphism `cc-thom`'s residual is about.**  The section pulled back on relative
cohomology, from the pair of the bundle to the pair of the base. -/
def lixSRel (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) (n : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n ⟶
      relCohomology (ZMod 2) (lixN dd)
        ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n :=
  relPullback (ZMod 2) (cmap (lixSectionTotal hGc hGu hGe))
    (lixSectionTotal_mapsTo hGc hGu hGe) n

end GroupApproximation.CharClass
