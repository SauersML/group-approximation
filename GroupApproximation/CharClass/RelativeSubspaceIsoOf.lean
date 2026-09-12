import GroupApproximation.CharClass.RelativeSubspaceIso
import GroupApproximation.Meta.AxiomGuard

/-!
# The five lemma over the pair sequence, and changing the subspace, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twins of `RelativeHomotopyInvariance.relPullback_bijective_of_absolute` and
`RelativeSubspaceIso.relPullback_id_bijective_of_subspace_iso`, with the coefficient ring a
parameter.  Nothing in either argument uses characteristic two: the three exactness
statements and the three naturality squares are already generic
(`exact_absToSub_relDeltaOf`, `exact_relDelta_relToAbsOf`, `exact_relToAbs_absToSubOf`,
`absToSub_naturality`, `relDelta_naturality`, `relToAbs_naturality`), and Mathlib's five
lemma is stated for modules over any ring.  So these are substitutions, `[CommRing K]`
throughout, and the `F₂` statements are their `K = ZMod 2` instances (`absPull_eq_absPullOf`
records that the vertical maps agree definitionally).

The odd side of Step C consumes both through `LIXStepCOddRelative`; at odd `p` it needs them
at `K = ZMod p`, which is what this file supplies.

## Main results

* `RelativeSupport.relPullback_bijective_of_absoluteOf` — the five lemma over `K`.
* `RelativeSupport.relPullback_id_bijective_of_subspace_isoOf` — changing the subspace by a
  cohomology isomorphism, over `K`, in every degree.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

variable {X Y : TopCat.{0}}

/-- The `F₂` vertical map is the `K = ZMod 2` instance of the generic one. -/
theorem absPull_eq_absPullOf (f : X ⟶ Y) (m : ℕ) : absPull f m = absPullOf (ZMod 2) f m := rfl

/-! ## 1. The five lemma over the sequence of the pair -/

/-- **A map of pairs bijective on both absolute theories is bijective on the relative
theory**, over any commutative ring.  Degree `n + 1`; degree `0` is outside the argument,
since the sequence of the pair has no term to the left of `H^0(Z, S)`. -/
theorem relPullback_bijective_of_absoluteOf (K : Type) [CommRing K] (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ)
    (habs : ∀ m, Function.Bijective (absPullOf K f m).hom)
    (hsub : ∀ m, Function.Bijective (subPullOf K f hf m).hom) :
    Function.Bijective (relPullback K f hf (n + 1)).hom :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (absToSub K B n).hom (relDelta K Y B n).hom
    (relToAbs K Y B (n + 1)).hom (absToSub K B (n + 1)).hom
    (absToSub K A n).hom (relDelta K X A n).hom
    (relToAbs K X A (n + 1)).hom (absToSub K A (n + 1)).hom
    (absPullOf K f n).hom (subPullOf K f hf n).hom (relPullback K f hf (n + 1)).hom
    (absPullOf K f (n + 1)).hom (subPullOf K f hf (n + 1)).hom
    (linearMap_comp_of_squareOf (absToSub_naturality K f hf n))
    (linearMap_comp_of_squareOf (relDelta_naturality K f hf n))
    (linearMap_comp_of_squareOf (relToAbs_naturality K f hf (n + 1)))
    (linearMap_comp_of_squareOf (absToSub_naturality K f hf (n + 1)))
    (exact_absToSub_relDeltaOf K Y B n) (exact_relDelta_relToAbsOf K Y B n)
    (exact_relToAbs_absToSubOf K Y B n)
    (exact_absToSub_relDeltaOf K X A n) (exact_relDelta_relToAbsOf K X A n)
    (exact_relToAbs_absToSubOf K X A n)
    (habs n).2 (hsub n) (habs (n + 1)) (hsub (n + 1)).1

/-! ## 2. The vertical maps for the identity on the ambient space -/

/-- Pulling back along the identity of the ambient space **is** the identity, over `K`. -/
theorem absPull_id_eqOf (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ) :
    absPullOf K (𝟙 X) m = 𝟙 ((cochainCx K X).homology m) := by
  show HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor K (ModuleCat.of K K)).map (𝟙 X).op) m = _
  rw [show ((𝟙 X).op : Opposite.op X ⟶ Opposite.op X) = 𝟙 (Opposite.op X) from rfl,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

theorem absPull_id_applyOf (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ)
    (a : (cochainCx K X).homology m) : (absPullOf K (𝟙 X) m).hom a = a := by
  rw [absPull_id_eqOf]
  rfl

/-- Pulling back along the identity of the ambient space is bijective, over `K`. -/
theorem absPull_idOf (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ) :
    Function.Bijective (absPullOf K (𝟙 X) m).hom := by
  rw [absPull_id_eqOf]
  exact ⟨fun _ _ hab => hab, fun a => ⟨a, rfl⟩⟩

/-- For the identity on the ambient space, the subspace vertical map **is** the pullback
along the inclusion of subspaces, over `K`. -/
theorem subPull_id_eqOf (K : Type) [CommRing K] {A B : Set X} (hAB : A ⊆ B) (m : ℕ) :
    (subPullOf K (𝟙 X) (fun _ hx => hAB hx) m).hom
      = (cohPullbackK K (subInclusion hAB) m).hom := rfl

/-! ## 3. Degree zero -/

theorem relPullback_id_bijective_zeroOf (K : Type) [CommRing K] {A B : Set X} (hAB : A ⊆ B)
    (hsub : ∀ k : ℕ, Function.Bijective (pull (K := K) (subInclusion hAB) k)) :
    Function.Bijective (relPullback K (𝟙 X) (fun _ hx => hAB hx) 0).hom := by
  have hf : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 X)) x ∈ B := fun _ hx => hAB hx
  -- the two squares, as equations between linear maps
  have hsq : (relToAbs K X A 0).hom.comp (relPullback K (𝟙 X) hf 0).hom
      = (absPullOf K (𝟙 X) 0).hom.comp (relToAbs K X B 0).hom :=
    linearMap_comp_of_squareOf (relToAbs_naturality K (𝟙 X) hf 0)
  have hsqa : (absToSub K A 0).hom.comp (absPullOf K (𝟙 X) 0).hom
      = (subPullOf K (𝟙 X) hf 0).hom.comp (absToSub K B 0).hom :=
    linearMap_comp_of_squareOf (absToSub_naturality K (𝟙 X) hf 0)
  have hjA : Function.Injective (relToAbs K X A 0).hom := injective_relToAbs_zero K X A
  have hjB : Function.Injective (relToAbs K X B 0).hom := injective_relToAbs_zero K X B
  constructor
  · -- injectivity: `j^*_A ∘ relPullback = absPull ∘ j^*_B` and the right side is injective
    have hcomp : Function.Injective
        ((relToAbs K X A 0).hom ∘ (relPullback K (𝟙 X) hf 0).hom) := by
      intro a b hab
      apply hjB
      apply (absPull_idOf K X 0).1
      have h1 := congrArg (fun L => L a) hsq
      have h2 := congrArg (fun L => L b) hsq
      simp only [LinearMap.comp_apply] at h1 h2
      rw [← h1, ← h2]
      exact hab
    exact Function.Injective.of_comp hcomp
  · -- surjectivity: chase the image of `j^*_A` back through the sequence of `(X, B)`
    intro a
    have hzero : (absToSub K B 0).hom ((relToAbs K X A 0).hom a) = 0 := by
      apply (hsub 0).1
      have h1 := congrArg (fun L => L ((relToAbs K X A 0).hom a)) hsqa
      simp only [LinearMap.comp_apply] at h1
      rw [subPull_id_eqOf K hAB 0] at h1
      show (cohPullbackK K (subInclusion hAB) 0).hom _ = (cohPullbackK K (subInclusion hAB) 0).hom 0
      rw [map_zero, ← h1]
      rw [absPull_id_applyOf K X 0]
      exact comp_apply_eq_zeroOf (relToAbs_comp_absToSub K X A 0) a
    obtain ⟨b, hb⟩ := relLES_exact_abs K X B 0 _ hzero
    refine ⟨b, hjA ?_⟩
    have h1 := congrArg (fun L => L b) hsq
    simp only [LinearMap.comp_apply] at h1
    rw [h1, hb, absPull_id_applyOf K X 0]

/-! ## 4. Changing the subspace -/

/-- **Changing the subspace by a cohomology isomorphism, over any ring.**  If `A ⊆ B` and the
inclusion `A ↪ B` induces bijections on `H^*(−; K)` in every degree, then the inclusion of
pairs `(X, A) → (X, B)` induces bijections on relative cohomology in every degree. -/
theorem relPullback_id_bijective_of_subspace_isoOf (K : Type) [CommRing K] {A B : Set X}
    (hAB : A ⊆ B)
    (hsub : ∀ k : ℕ, Function.Bijective (pull (K := K) (subInclusion hAB) k)) (n : ℕ) :
    Function.Bijective (relPullback K (𝟙 X) (fun _ hx => hAB hx) n).hom := by
  cases n with
  | zero => exact relPullback_id_bijective_zeroOf K hAB hsub
  | succ m =>
      refine relPullback_bijective_of_absoluteOf K (𝟙 X) (fun _ hx => hAB hx) m
        (fun k => absPull_idOf K X k) (fun k => ?_)
      rw [subPull_id_eqOf K hAB k]
      exact hsub k

end

end RelativeSupport

/-! Audited on every build. -/

#audit_axioms RelativeSupport.relPullback_bijective_of_absoluteOf
#audit_axioms RelativeSupport.relPullback_id_bijective_of_subspace_isoOf

end GroupApproximation.CharClass
