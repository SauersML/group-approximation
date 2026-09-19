import GroupApproximation.CharClass.RelativeSubspaceIso
import GroupApproximation.CharClass.BundleGysinPieces
import GroupApproximation.CharClass.BundleProjInclRange
import GroupApproximation.CharClass.BundleTautPieces

/-!
# The Thom bridge, step three: the hyperplane replaces the punctured space

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

Steps one and two (`ThomBridgeChart`) carry `H^n(P(p⊕1), P(p⊕1) ∖ Z)` to
`H^n(E, E ∖ 0)`.  This step replaces the punctured projectivisation by the
hyperplane, which is what lets Leray–Hirsch — stated about `P(p)` — reach the
pair:

```text
H^n(P(p⊕1), P(p)) ≅ H^n(P(p⊕1), P(p⊕1) ∖ Z).
```

`cc-relative`'s `RelativeSupport.relPullback_id_bijective_of_subspace_iso` is the
homological content and is landed.  It wants two **subsets of one ambient**, so
the hyperplane has to be presented as `Set.range (Bundle.projIncl p)` rather than
through the map, and it wants the subspace inclusion to be an isomorphism on
cohomology.

## The topological input, and it is discharged in this file

That the inclusion of the hyperplane into the complement of the zero section is a
homotopy equivalence.  `cc-bundle`'s `notZeroOpensHomotopyEquivProj` is that
equivalence with `Proj p` on the other side, and their
`notZeroOpensHomotopyEquivProj_invFun` says its homotopy inverse *is* the
inclusion.  `hyperplane_hsub` below discharges it, so `bridgeHyperplane`'s named
hypothesis is not open.

**Correction, and the earlier text was wrong.**  This docstring used to record
that no Mathlib route at the pin produces `X ≃ₜ ↥(Set.range f)` from a closed
embedding, and that the homeomorphism onto the range therefore had to be
requested.  That absence claim is **false**.  `Topology.IsEmbedding.toHomeomorph`
is exactly that, at `Mathlib/Topology/Homeomorph/Lemmas.lean:412` at the pinned
revision, and `cc-bundle`'s `projInclHomeoRange` is one application of it.  I
reached the claim by truncating my own search output and reporting the truncation
as an absence.

A false absence claim is worse in a docstring than a wrong proof: a wrong proof
fails at the probe, while this one sends a reader hunting for a lemma that is
already there.  It is recorded rather than deleted so that the failure is
attributable.

## Main declaration

* `bridgeHyperplane` — the replacement, over that one input.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The hyperplane misses the zero section.**  Immediate from `cc-bundle`'s
membership lemma; this is the containment `cc-relative`'s corollary needs. -/
theorem range_projIncl_subset_notZero (p : Bundle X ι) :
    (Set.range (Bundle.projIncl p) : Set ↥(TopCat.of (Bundle.Proj p.plusOne)))
      ⊆ (Bundle.notZeroOpensSet p : Set ↥(TopCat.of (Bundle.Proj p.plusOne))) := by
  rintro w ⟨z, rfl⟩
  exact (Bundle.projIncl_mem_notZeroSet p z).2

/-- **Step three of the Thom bridge.**  Replacing the punctured projectivisation
by the hyperplane, over the one topological input: that the subspace inclusion is
an isomorphism on cohomology in every degree.

`cc-bundle`'s homotopy equivalence supplies that as soon as the hyperplane is
presented as a subset; until then it is named rather than assumed silently. -/
theorem bridgeHyperplane (p : Bundle X ι)
    (hsub : ∀ k : ℕ,
      Function.Bijective (pull (subInclusion (range_projIncl_subset_notZero p)) k))
    (n : ℕ) :
    Function.Bijective
      (relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hx => range_projIncl_subset_notZero p hx) n).hom :=
  RelativeSupport.relPullback_id_bijective_of_subspace_iso
    (range_projIncl_subset_notZero p) hsub n

/-! ## Discharging the input -/

/-- The subspace inclusion, precomposed with `cc-bundle`'s homeomorphism onto the
range, **is** the homotopy inverse of their equivalence.  Both identifications
hold by `rfl`, so the morphism equality is definitional. -/
theorem incl_comp_eq_invFun [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun
        ≫ subInclusion (range_projIncl_subset_notZero p))
      = cmap (Bundle.notZeroOpensHomotopyEquivProj p).symm.toFun := rfl

/-- **The named input of `bridgeHyperplane`, discharged.**  The inclusion is a
homotopy equivalence because it is the homotopy inverse composed with a
homeomorphism, so its pullback is bijective in every degree. -/
theorem hyperplane_hsub [CompactSpace X] [T2Space X] (p : Bundle X ι) (k : ℕ) :
    Function.Bijective (pull (subInclusion (range_projIncl_subset_notZero p)) k) := by
  have hcomp : ∀ a, pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k
      (pull (subInclusion (range_projIncl_subset_notZero p)) k a)
      = pull (cmap (Bundle.notZeroOpensHomotopyEquivProj p).symm.toFun) k a := by
    intro a
    rw [← pull_comp]
    exact congrArg (fun f => pull f k a) (incl_comp_eq_invFun p)
  have hhomeo := (pullEquivOfHomeomorph (Bundle.projInclHomeoRange p) k).bijective
  have hinv := (pullEquivOfHomotopyEquiv
    (Bundle.notZeroOpensHomotopyEquivProj p).symm k).bijective
  constructor
  · intro a b hab
    have h1 := congrArg (pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k) hab
    rw [hcomp, hcomp] at h1
    exact hinv.1 h1
  · intro b
    obtain ⟨a, ha⟩ := hinv.2 (pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k b)
    refine ⟨a, hhomeo.1 ?_⟩
    show pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k
        (pull (subInclusion (range_projIncl_subset_notZero p)) k a)
      = pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k b
    rw [hcomp]
    exact ha

/-! Printed on every build. -/

#print axioms bridgeHyperplane

#print axioms hyperplane_hsub

end

end GroupApproximation.CharClass
