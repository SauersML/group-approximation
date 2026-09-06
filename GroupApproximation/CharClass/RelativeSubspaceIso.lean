import GroupApproximation.CharClass.RelativeHomotopyInvariance
import GroupApproximation.CharClass.MayerVietorisRestriction

/-!
# Changing the subspace by a cohomology isomorphism

For `A ⊆ B` inside one ambient space `X`, the inclusion of pairs
`(X, A) → (X, B)` — the identity on the ambient space — induces bijections on
relative cohomology as soon as the inclusion `A ↪ B` induces bijections on
absolute cohomology.  This is the bridge `cc-thom`'s Thom class needs: their class
lives in `H^*(E, E ∖ 0)` and their Leray–Hirsch data in `H^*(P(E ⊕ 1), P(E))`, and
the two models are compared by exactly this move, with the subspace isomorphism
coming from `cc-bundle`'s homotopy equivalence `notZeroHomotopyEquivProj`.

Both ambient spaces are the same, and it is not contractible, so there is no
connecting-map shortcut here: the argument is genuinely the five lemma over the
two long exact sequences of `(X, A)` and `(X, B)`, in which two of the four outer
vertical maps are literally identities.

Degrees `n + 1` come from `relPullback_bijective_of_absolute`.  Degree `0` is a
separate three-step chase, because the sequence of a pair has no term to the left
of `H^0(X, S)` and the five lemma has nothing to stand on; what replaces it is
that `j^*` is *injective* in degree `0`
(`HomologicalComplex.mono_homologyMap_of_mono_of_not_rel`, since no degree
precedes `0` in the cochain shape).

## Main results

* `RelativeSupport.relPullback_id_bijective_of_subspace_iso` — the statement
  `cc-thom` consumes, in every degree.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The two vertical maps for the identity on the ambient space -/

/-- Pulling back along the identity of the ambient space **is** the identity.  Proved
once and reused: the two `Functor` namespaces make `Functor.map_id` ambiguous, so
the categorical one is named in full. -/
theorem absPull_id_eq (X : TopCat.{0}) (m : ℕ) :
    absPull (𝟙 X) m = 𝟙 ((cochainCx (ZMod 2) X).homology m) := by
  show HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
      (𝟙 X).op) m = _
  rw [show ((𝟙 X).op : Opposite.op X ⟶ Opposite.op X) = 𝟙 (Opposite.op X) from rfl,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

theorem absPull_id_apply (X : TopCat.{0}) (m : ℕ)
    (a : (cochainCx (ZMod 2) X).homology m) : (absPull (𝟙 X) m).hom a = a := by
  rw [absPull_id_eq]
  rfl

/-- Pulling back along the identity of the ambient space is bijective. -/
theorem absPull_id (X : TopCat.{0}) (m : ℕ) : Function.Bijective (absPull (𝟙 X) m).hom := by
  rw [absPull_id_eq]
  exact ⟨fun _ _ hab => hab, fun a => ⟨a, rfl⟩⟩

/-- For the identity on the ambient space, the subspace vertical map **is** the
pullback along the inclusion of subspaces. -/
theorem subPull_id_eq {A B : Set X} (hAB : A ⊆ B) (m : ℕ) :
    (subPull (𝟙 X) (fun _ hx => hAB hx) m).hom = (cohPullback (subInclusion hAB) m).hom := rfl

/-! ## 2. Degree zero -/

/-- In degree `0` the map `j^*` is injective: no degree precedes `0`, so the
relative cocycles inject into the absolute ones. -/
theorem injective_relToAbs_zero (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) :
    Function.Injective (relToAbs R X S 0).hom := by
  haveI : Mono ((relInclusion R X S).f 0) :=
    (ModuleCat.mono_iff_injective _).2 (fun _ _ hab => Subtype.ext hab)
  haveI : Mono (relToAbs R X S 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (relInclusion R X S) 0
      (fun i hi => Nat.succ_ne_zero i hi)
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

theorem relPullback_id_bijective_zero {A B : Set X} (hAB : A ⊆ B)
    (hsub : ∀ k : ℕ, Function.Bijective (pull (subInclusion hAB) k)) :
    Function.Bijective (relPullback (ZMod 2) (𝟙 X) (fun _ hx => hAB hx) 0).hom := by
  have hf : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 X)) x ∈ B := fun _ hx => hAB hx
  -- the three squares, as equations between linear maps
  have hsq : (relToAbs (ZMod 2) X A 0).hom.comp
        (relPullback (ZMod 2) (𝟙 X) hf 0).hom
      = (absPull (𝟙 X) 0).hom.comp (relToAbs (ZMod 2) X B 0).hom :=
    linearMap_comp_of_square (relToAbs_naturality (ZMod 2) (𝟙 X) hf 0)
  have hsqa : (absToSub (ZMod 2) A 0).hom.comp (absPull (𝟙 X) 0).hom
      = (subPull (𝟙 X) hf 0).hom.comp (absToSub (ZMod 2) B 0).hom :=
    linearMap_comp_of_square (absToSub_naturality (ZMod 2) (𝟙 X) hf 0)
  have hjA : Function.Injective (relToAbs (ZMod 2) X A 0).hom :=
    injective_relToAbs_zero (ZMod 2) X A
  have hjB : Function.Injective (relToAbs (ZMod 2) X B 0).hom :=
    injective_relToAbs_zero (ZMod 2) X B
  constructor
  · -- injectivity: `j^*_A ∘ relPullback = absPull ∘ j^*_B` and the right side is injective
    have hcomp : Function.Injective
        ((relToAbs (ZMod 2) X A 0).hom ∘ (relPullback (ZMod 2) (𝟙 X) hf 0).hom) := by
      intro a b hab
      apply hjB
      apply (absPull_id X 0).1
      have h1 := congrArg (fun L => L a) hsq
      have h2 := congrArg (fun L => L b) hsq
      simp only [LinearMap.comp_apply] at h1 h2
      rw [← h1, ← h2]
      exact hab
    exact Function.Injective.of_comp hcomp
  · -- surjectivity: chase the image of `j^*_A` back through the sequence of `(X, B)`
    intro a
    have hzero : (absToSub (ZMod 2) B 0).hom ((relToAbs (ZMod 2) X A 0).hom a) = 0 := by
      apply (hsub 0).1
      have h1 := congrArg (fun L => L ((relToAbs (ZMod 2) X A 0).hom a)) hsqa
      simp only [LinearMap.comp_apply] at h1
      rw [subPull_id_eq hAB 0] at h1
      show (cohPullback (subInclusion hAB) 0).hom _ = (cohPullback (subInclusion hAB) 0).hom 0
      rw [map_zero, ← h1]
      rw [absPull_id_apply X 0]
      exact comp_apply_eq_zero (relToAbs_comp_absToSub (ZMod 2) X A 0) a
    obtain ⟨b, hb⟩ := relLES_exact_abs (ZMod 2) X B 0 _ hzero
    refine ⟨b, hjA ?_⟩
    have h1 := congrArg (fun L => L b) hsq
    simp only [LinearMap.comp_apply] at h1
    rw [h1, hb, absPull_id_apply X 0]

/-! ## 3. The statement `cc-thom` consumes -/

/-- **Changing the subspace by a cohomology isomorphism.**  If `A ⊆ B` and the
inclusion `A ↪ B` induces bijections on cohomology in every degree, then the
inclusion of pairs `(X, A) → (X, B)` induces bijections on relative cohomology in
every degree. -/
theorem relPullback_id_bijective_of_subspace_iso {A B : Set X} (hAB : A ⊆ B)
    (hsub : ∀ k : ℕ, Function.Bijective (pull (subInclusion hAB) k)) (n : ℕ) :
    Function.Bijective (relPullback (ZMod 2) (𝟙 X) (fun _ hx => hAB hx) n).hom := by
  cases n with
  | zero => exact relPullback_id_bijective_zero hAB hsub
  | succ m =>
      refine relPullback_bijective_of_absolute (𝟙 X) (fun _ hx => hAB hx) m
        (fun k => absPull_id X k) (fun k => ?_)
      rw [subPull_id_eq hAB k]
      exact hsub k

end

end RelativeSupport

end GroupApproximation.CharClass
