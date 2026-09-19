import GroupApproximation.CharClass.LIXThomClassTerm
import GroupApproximation.CharClass.LIXBaseConnected
import GroupApproximation.CharClass.LIXRestrictionMap

/-!
# `hres` is one nonvanishing statement

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`lix_topClass_ne_zero_of_local` takes `hres`, the injectivity of `cc-lix-odd`'s
`lixRes`.  Injectivity is more than the situation contains, because the **source
is a line**: the degreewise Thom algebra identifies the relative group of the
bundle pair with `H^0` of the base, and `LIXBaseConnected` says that is one
dimensional over `F₂`.  A linear map out of a line is injective exactly when it
does not kill the generator, and the generator is `lixThomClassTerm`.

So `hres` **is** the single statement

```text
(lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0,
```

the nonvanishing of the relative Euler class at the section's zero.  Nothing is
lost in the reduction: the two are equivalent, and the converse direction is
immediate from injectivity and `lixThomClassTerm_ne_zero`.

**This is not excision.**  `cc-bundle`'s `BundleTotalOver` and `cc-lix-odd`'s
`LIXRestrictionMap` both record why: the excised set would be the part of the
total space over the complement of the ball, and its closure contains
zero-section points, which are exactly what the punctured set omits.  I asserted
the excision route earlier tonight and was wrong; the rank count refutes it,
since the full relative group has rank the number of components of the base and
the local one has rank one.

## Main declarations

* `cohCastEquiv` — a degree transport, as a linear equivalence.
* `injective_of_line` — a map out of a line is injective iff it spares the generator.
* `lixRelLine` — **the relative group of the bundle pair is a line.**
* `injective_lixRes_of_ne_zero` — **`hres`, from the nonvanishing.**
* `ne_zero_of_injective_lixRes` — the converse, so the reduction loses nothing.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

/-! ## 1. Two pieces of linear algebra -/

/-- A degree transport, as a linear equivalence. -/
def cohCastEquiv {Z : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    Hmod2 Z m ≃ₗ[ZMod 2] Hmod2 Z m' where
  toFun := cohCast h
  invFun := cohCast h.symm
  map_add' := cohCast_add h
  map_smul' s a := cohCast_smul h s a
  left_inv _ := by subst h; rfl
  right_inv _ := by subst h; rfl

/-- **A linear map out of a line is injective as soon as it spares one nonzero
element.**  Over `F₂` a line has exactly two elements, so any nonzero class *is*
the generator. -/
theorem injective_of_line {A B : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] (e : A ≃ₗ[ZMod 2] ZMod 2)
    (f : A →ₗ[ZMod 2] B) {a₀ : A} (ha₀ : a₀ ≠ 0) (hf : f a₀ ≠ 0) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun a ha => ?_
  by_contra hane
  have h1 : e a ≠ 0 := fun h => hane (by simpa using congrArg e.symm h)
  have h2 : e a₀ ≠ 0 := fun h => ha₀ (by simpa using congrArg e.symm h)
  have key : ∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y := by decide
  exact hf (by rw [← e.injective (key _ _ h1 h2)]; exact ha)

/-! ## 2. The relative group of the bundle pair is a line -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **The relative group of the mapping-torus bundle pair is a line.**  The
degreewise Thom algebra identifies it with `H^0` of the base, and the base is
path-connected. -/
def lixRelLine (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)) ≃ₗ[ZMod 2] ZMod 2 :=
  (ThomDeg.thomEquiv
      (fun i => chernMul (hyperLH_range (lixBundle G hGc hGu) (lixRank dd)
        (rank_lixBundle G hGc hGu) (one_le_lixRank_dd dd)) i)
      (thomJmTotal (lixBundle G hGc hGu) (lixLHplus hGc hGu))
      (injective_thomJmTotal (lixBundle G hGc hGu) (one_le_lixRank_dd dd)
        (rank_lixBundle G hGc hGu) (lixLHplus hGc hGu))
      (range_thomJmTotal (lixBundle G hGc hGu) (rank_lixBundle G hGc hGu)
        (one_le_lixRank_dd dd) (lixLHplus hGc hGu))).trans
    ((cohCastEquiv (Z := TopCat.of (↥sphereOne × baseM dd))
        (by rw [Fin.val_last]; omega)).trans
      (cohZeroEquiv (TopCat.of (↥sphereOne × baseM dd))))

/-! ## 3. `hres` -/

/-- **`hres`, from the nonvanishing of the relative Euler class.**  This is the
whole of the injectivity `lix_topClass_ne_zero_of_local` asks for. -/
theorem injective_lixRes_of_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hne : (lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0) :
    Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom :=
  injective_of_line (lixRelLine hGc hGu) (lixRes hGc hGu (2 * lixRank dd)).hom
    (lixThomClassTerm_ne_zero hGc hGu) hne

/-- The converse, so that the reduction loses nothing: an injective restriction
spares the Thom class, because the Thom class is nonzero. -/
theorem ne_zero_of_injective_lixRes (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hinj : Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom) :
    (lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0 := by
  intro h0
  exact lixThomClassTerm_ne_zero hGc hGu (hinj (h0.trans (map_zero _).symm))

/-! Printed on every build. -/

#print axioms injective_lixRes_of_ne_zero

end ThomChernDeg

end

end GroupApproximation.CharClass
