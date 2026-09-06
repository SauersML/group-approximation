import GroupApproximation.CharClass.BundlePairs
import GroupApproximation.CharClass.RelativeLocal

/-!
# The bundle pair over a trivialising neighbourhood

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`ThomStepCSection.lean` reduced Step C's residual to `SectionDetectsThom`, that
the section pullback does not kill the Thom class.  Closing it means computing the
Thom class over a trivialising neighbourhood, and the first step of that is to
replace the bundle pair by a product pair.

That step is a composition of two things that already exist and that fit with no
adaptation:

* `cc-bundle`'s `Bundle.totalTrivStd_image_punctured` says the standard local
  trivialisation carries the complement of the zero section **onto**
  `U × (ℂ^r ∖ 0)` — an image equation, which is exactly the hypothesis shape of
* `cc-relative`'s `relCohomologyCongr`, homeomorphism invariance of pairs.

So the bridge is one definition.  It is recorded here rather than in either
owner's file, because it is the seam between them and belongs to the consumer.

## What this does **not** yet give

The Thom class over the neighbourhood is the local generator only once
`H^{2r}(U × ℂ^r, U × (ℂ^r ∖ 0); F₂)` is identified with `H^0(U; F₂)`.  That is a
*relative* Künneth with a contractible second factor, and the Künneth work in the
tree is absolute.  It is the one remaining input and it is asked for by name;
see the lane report.

## Main declarations

* `bundlePairTrivIso` — the bundle pair over a trivialising neighbourhood is the
  product pair `(U × ℂ^r, U × (ℂ^r ∖ 0))`.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The bundle pair over a trivialising neighbourhood is a product pair.**
`cc-bundle`'s image equation for the standard local trivialisation, fed to
`cc-relative`'s homeomorphism invariance of pairs. -/
def bundlePairTrivIso (p : Bundle X ι) (x₀ : X) (r : ℕ) (hr : p.rank x₀ = r) (n : ℕ) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total (p.restrictTo (Bundle.trivSet p x₀))))
        {w : Bundle.Total (p.restrictTo (Bundle.trivSet p x₀)) |
          (w : ↥(Bundle.trivSet p x₀) × (ι → ℂ))
            ∈ Bundle.puncturedSet (p.restrictTo (Bundle.trivSet p x₀))} n
      ≅ relCohomology (ZMod 2)
        (TopCat.of (↥(Bundle.trivSet p x₀) × (Fin r → ℂ)))
        {q : ↥(Bundle.trivSet p x₀) × (Fin r → ℂ) | q.2 ≠ 0} n :=
  relCohomologyCongr (p.totalTrivStd x₀ r hr) _ _
    (Bundle.totalTrivStd_image_punctured p x₀ r hr) n

/-! ## 2. A retracted map of pairs is injective on relative cohomology -/

/-- **A map of pairs with a retraction is injective on relative cohomology.**

This is the step that makes the Thom class of a *trivial* bundle over a
neighbourhood computable with no Künneth theorem of pairs.  The projection
`V × ℂ^r → ℂ^r` is retracted by any fibre inclusion `i_v`, so pulling back along
it is injective, and the local generator therefore stays nonzero upstairs.
Combined with the relative group over a path-connected `V` being a line — which
is `ThomFreeDegreewise.thomEquiv` at the trivial bundle together with
`H^0(V; F₂) ≅ F₂` — the pulled-back generator *is* the Thom class, since a line
has only one nonzero element. -/
theorem relPullback_injective_of_retraction (R : Type) [CommRing R]
    {X Y : TopCat.{0}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ y ∈ B, (ConcreteCategory.hom g) y ∈ A)
    (hfg : f ≫ g = 𝟙 X) (n : ℕ) :
    Function.Injective (relPullback R g hg n).hom := by
  have hcomp : ∀ x ∈ A, (ConcreteCategory.hom (f ≫ g)) x ∈ A :=
    fun x hx => hg _ (hf x hx)
  have hstep : relPullback R g hg n ≫ relPullback R f hf n = 𝟙 _ := by
    rw [← relPullback_comp R f g hf hg hcomp n, relPullback_eq_of_eq R hfg hcomp n,
      relPullback_id]
  intro a b hab
  have h1 := congrArg (relPullback R f hf n).hom hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hstep] at h1
  simpa using h1

end

end GroupApproximation.CharClass
