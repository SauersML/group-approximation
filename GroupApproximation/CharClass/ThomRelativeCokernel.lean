import GroupApproximation.CharClass.RelativeLES

/-!
# When the restriction is injective, the relative group is a cokernel

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

This is the homological core of `cc-bundle`'s route to the Thom class of a
trivial bundle, isolated from the geometry so that it can be checked on its own.

In the long exact sequence of a pair, suppose the restriction `i^*` is
**injective in every degree**.  Then two things follow at once:

* the map out of the relative group is zero, because its image is the kernel of
  an injective map, so the connecting map is **surjective**;
* the kernel of the connecting map is exactly the image of `i^*`, which is
  ordinary exactness.

So the relative group is the **cokernel** of the restriction:

```text
H^{n+1}(X, A)  ≅  H^n(A) ⧸ range i^*.
```

Applied to `(U × ℂ^r, U × S^{2r-1})`, where the restriction is the inclusion of
the first Künneth summand and is injective because a slice retracts the
projection, this gives the relative group as the base's cohomology shifted by the
fibre dimension — with **no relative Künneth and no hypothesis on the base**.
That was the point of the route: the earlier plan needed a contractible
trivialising neighbourhood, which is a property of the base and false in general.

Nothing here is about bundles, spheres or products.  It is the pair sequence and
one injectivity hypothesis.

## Main declarations

* `relDelta_surjective_of_injective` — the connecting map is onto.
* `ker_relDelta_eq_range_absToSub` — its kernel is the image of the restriction.
* `relQuotEquiv` — **the relative group is the cokernel of the restriction.**
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

/-- **The connecting map is surjective** when the restriction is injective one
degree up.  The image of `j^*` lies in the kernel of `i^*`, which is trivial, so
`j^*` is zero and exactness at the relative group makes `δ` onto. -/
theorem relDelta_surjective_of_injective (R : Type) [CommRing R] (X : TopCat.{0})
    (A : Set X) (n : ℕ)
    (hinj : Function.Injective (absToSub R A (n + 1)).hom) :
    Function.Surjective (relDelta R X A n).hom := by
  intro a
  refine relLES_exact_rel R X A n a (hinj ?_)
  rw [map_zero]
  have hcomp := relToAbs_comp_absToSub R X A (n + 1)
  have := congrArg (fun f : relCohomology R X A (n + 1) ⟶ _ => f.hom a) hcomp
  simpa using this

/-- **The kernel of the connecting map is the image of the restriction.**  One
inclusion is exactness at `H^n(A)`, the other is that the two maps compose to
zero. -/
theorem ker_relDelta_eq_range_absToSub (R : Type) [CommRing R] (X : TopCat.{0})
    (A : Set X) (n : ℕ) :
    LinearMap.ker (relDelta R X A n).hom = LinearMap.range (absToSub R A n).hom := by
  apply le_antisymm
  · intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨b, hb⟩ := relLES_exact_sub R X A n a ha
    exact ⟨b, hb⟩
  · rintro a ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    have hcomp := absToSub_comp_relDelta R X A n
    have := congrArg (fun f : (cochainCx R X).homology n ⟶ _ => f.hom b) hcomp
    simpa using this

/-- **The relative group is the cokernel of the restriction.**  This is the whole
homological content of the route: no Künneth of pairs, no contractibility, just
the pair sequence and one injectivity hypothesis. -/
noncomputable def relQuotEquiv (R : Type) [CommRing R] (X : TopCat.{0})
    (A : Set X) (n : ℕ)
    (hinj : Function.Injective (absToSub R A (n + 1)).hom) :
    ((cochainCx R (TopCat.of A)).homology n ⧸ LinearMap.range (absToSub R A n).hom)
      ≃ₗ[R] relCohomology R X A (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (ker_relDelta_eq_range_absToSub R X A n).symm).trans
    ((relDelta R X A n).hom.quotKerEquivOfSurjective
      (relDelta_surjective_of_injective R X A n hinj))

end

end GroupApproximation.CharClass
