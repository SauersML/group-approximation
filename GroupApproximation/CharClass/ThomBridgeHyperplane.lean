import GroupApproximation.CharClass.RelativeSubspaceIso
import GroupApproximation.CharClass.BundleGysinPieces

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

## The single topological input

That the inclusion of the hyperplane into the complement of the zero section is a
homotopy equivalence.  `cc-bundle`'s `notZeroOpensHomotopyEquivProj` is that
equivalence with `Proj p` on the other side, and their
`notZeroOpensHomotopyEquivProj_invFun` says its homotopy inverse *is* the
inclusion — so the content exists, but not yet with the hyperplane presented as a
subset.

Searched for a Mathlib route at the pin: `IsEmbedding.toHomeomorph`,
`toHomeomorphOfIsInducing`, `Homeomorph.ofIsEmbedding`, and every `def
toHomeomorph` in `Mathlib/Topology`.  None produces `X ≃ₜ ↥(Set.range f)` from a
closed embedding at this revision, so the homeomorphism onto the range is not a
one-liner and is named here rather than invented.  `cc-bundle` has the request.

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

/-! Printed on every build. -/

#print axioms bridgeHyperplane

end

end GroupApproximation.CharClass
