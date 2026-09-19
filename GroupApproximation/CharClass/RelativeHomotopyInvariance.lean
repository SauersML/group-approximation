import GroupApproximation.CharClass.RelativeLocalModel
import Mathlib.Algebra.FiveLemma

/-!
# A map of pairs that is an isomorphism on both absolute groups is one on the relative group

The five lemma over the long exact sequence of the pair: if a map of pairs
`f : (X, A) → (Y, B)` induces bijections on the cohomology of the ambient spaces
and on the cohomology of the subspaces, in every degree, then it induces
bijections on the relative cohomology.  This is what makes relative cohomology
homotopy invariant, without any chain-level homotopy: feed it two absolute
homotopy equivalences.

Every ingredient is already green.  The three naturality squares of
`RelativeFunctorial.lean` give the map between the two long exact sequences, the
three exactness statements and three composite-zero facts of `RelativeLES.lean`
give exactness of both rows, and Mathlib's
`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`
(`Mathlib/Algebra/FiveLemma.lean`) is the five lemma itself, stated in exactly the
unbundled form this needs.  Nothing here is a diagram chase written by hand.

**The degree.** The conclusion is in degree `n + 1`, never in degree `0`.  The
five lemma needs a term to the left of the relative group, and in degree `0` the
sequence of the pair has none, so degree `0` is genuinely outside this argument
rather than merely unproved here.

## Main results

* `RelativeSupport.relPullback_bijective_of_absolute` — the five lemma applied to
  the pair sequence.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

variable {X Y : TopCat.{0}}

/-! ## 0. Two small bridges between the categorical and unbundled forms -/

/-- A composite of `ModuleCat` morphisms that vanishes, read on elements. -/
theorem comp_apply_eq_zero {M N P : ModuleCat.{0} (ZMod 2)} {u : M ⟶ N} {v : N ⟶ P}
    (h : u ≫ v = 0) (x : M) : v.hom (u.hom x) = 0 := by
  rw [← ModuleCat.comp_apply, h]
  rfl

/-- `Function.Exact` from the two halves this development produces: the composite
vanishes, and every element killed by the second map is hit by the first. -/
theorem exact_of_comp_of_mem_range {M N P : ModuleCat.{0} (ZMod 2)} (u : M ⟶ N) (v : N ⟶ P)
    (hcomp : u ≫ v = 0) (hker : ∀ y, v.hom y = 0 → ∃ x, u.hom x = y) :
    Function.Exact u.hom v.hom := by
  intro y
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hker y h
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    exact comp_apply_eq_zero hcomp x

/-- A commuting square of `ModuleCat` morphisms, as a composition of linear maps in
the orientation Mathlib's five lemma expects. -/
theorem linearMap_comp_of_square {M₁ M₂ N₁ N₂ : ModuleCat.{0} (ZMod 2)}
    {a : M₁ ⟶ M₂} {b : M₂ ⟶ N₂} {c : M₁ ⟶ N₁} {d : N₁ ⟶ N₂}
    (h : a ≫ b = c ≫ d) : d.hom.comp c.hom = b.hom.comp a.hom := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← ModuleCat.comp_apply,
    ← ModuleCat.comp_apply, h]

/-! ## 1. The two absolute pullbacks of a map of pairs -/

/-- The pullback on the cohomology of the ambient spaces. -/
abbrev absPull (f : X ⟶ Y) (m : ℕ) :
    (cochainCx (ZMod 2) Y).homology m ⟶ (cochainCx (ZMod 2) X).homology m :=
  HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map f.op) m

/-- The pullback on the cohomology of the subspaces. -/
abbrev subPull (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (m : ℕ) :
    (cochainCx (ZMod 2) (TopCat.of B)).homology m ⟶
      (cochainCx (ZMod 2) (TopCat.of A)).homology m :=
  HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
      (restrictPairMap f hf).op) m

/-! ## 2. Exactness of the two rows -/

/-- Exactness at `H^n(A)`: the restriction, then the connecting map. -/
theorem exact_absToSub_relDelta (Z : TopCat.{0}) (S : Set Z) (n : ℕ) :
    Function.Exact (absToSub (ZMod 2) S n).hom (relDelta (ZMod 2) Z S n).hom :=
  exact_of_comp_of_mem_range _ _ (absToSub_comp_relDelta (ZMod 2) Z S n)
    (fun y hy => relLES_exact_sub (ZMod 2) Z S n y hy)

/-- Exactness at `H^{n+1}(Z, S)`: the connecting map, then `j^*`. -/
theorem exact_relDelta_relToAbs (Z : TopCat.{0}) (S : Set Z) (n : ℕ) :
    Function.Exact (relDelta (ZMod 2) Z S n).hom (relToAbs (ZMod 2) Z S (n + 1)).hom :=
  exact_of_comp_of_mem_range _ _ (relDelta_comp_relToAbs (ZMod 2) Z S n)
    (fun y hy => relLES_exact_rel (ZMod 2) Z S n y hy)

/-- Exactness at `H^{n+1}(Z)`: `j^*`, then the restriction. -/
theorem exact_relToAbs_absToSub (Z : TopCat.{0}) (S : Set Z) (n : ℕ) :
    Function.Exact (relToAbs (ZMod 2) Z S (n + 1)).hom (absToSub (ZMod 2) S (n + 1)).hom :=
  exact_of_comp_of_mem_range _ _ (relToAbs_comp_absToSub (ZMod 2) Z S (n + 1))
    (fun y hy => relLES_exact_abs (ZMod 2) Z S (n + 1) y hy)

/-! ## 3. The five lemma over the sequence of the pair -/

/-- **A map of pairs bijective on both absolute theories is bijective on the
relative theory.**  Degree `n + 1`; degree `0` is outside the argument, since the
sequence of the pair has no term to the left of `H^0(Z, S)`. -/
theorem relPullback_bijective_of_absolute (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ)
    (habs : ∀ m, Function.Bijective (absPull f m).hom)
    (hsub : ∀ m, Function.Bijective (subPull f hf m).hom) :
    Function.Bijective (relPullback (ZMod 2) f hf (n + 1)).hom :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (absToSub (ZMod 2) B n).hom (relDelta (ZMod 2) Y B n).hom
    (relToAbs (ZMod 2) Y B (n + 1)).hom (absToSub (ZMod 2) B (n + 1)).hom
    (absToSub (ZMod 2) A n).hom (relDelta (ZMod 2) X A n).hom
    (relToAbs (ZMod 2) X A (n + 1)).hom (absToSub (ZMod 2) A (n + 1)).hom
    (absPull f n).hom (subPull f hf n).hom (relPullback (ZMod 2) f hf (n + 1)).hom
    (absPull f (n + 1)).hom (subPull f hf (n + 1)).hom
    (linearMap_comp_of_square (absToSub_naturality (ZMod 2) f hf n))
    (linearMap_comp_of_square (relDelta_naturality (ZMod 2) f hf n))
    (linearMap_comp_of_square (relToAbs_naturality (ZMod 2) f hf (n + 1)))
    (linearMap_comp_of_square (absToSub_naturality (ZMod 2) f hf (n + 1)))
    (exact_absToSub_relDelta Y B n) (exact_relDelta_relToAbs Y B n)
    (exact_relToAbs_absToSub Y B n)
    (exact_absToSub_relDelta X A n) (exact_relDelta_relToAbs X A n)
    (exact_relToAbs_absToSub X A n)
    (habs n).2 (hsub n) (habs (n + 1)) (hsub (n + 1)).1

end

end RelativeSupport

end GroupApproximation.CharClass
