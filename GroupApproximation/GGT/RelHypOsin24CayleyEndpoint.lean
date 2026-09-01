import GroupApproximation.GGT.RelHypOsin24CayleyLeaf
import GroupApproximation.GGT.RelHypOsinTheorem24Repaired

/-!
# The Fournier-Facio quotient, over the fourth-generation leaf

`GGT/RelHypOsin24CayleyLeaf.lean` states Osin's Theorem 2.4 at the relative
Cayley graph; `GGT/RelHypOsin24CayleyWitness.lean` shows the witness that
refutes the three earlier generations is not a model of it.  This module
re-derives the manuscript's small-cancellation quotient from the new leaf, so
that the chain to `FournierFacioQuotientStatement` no longer passes through a
refuted hypothesis.

The assembly is `GGT/RelHypOsinTheorem24Final.lean`'s, clause for clause, with
three differences forced by the change of leaf:

* the design produces the **relative generating set** `X` -- one geometry, and
  then a relator family for every length demand `rho` -- rather than an abstract
  length function.  It costs the design nothing extra: it already receives
  `IsRelativelyHyperbolic`, and `isRelativelyHyperbolic_iff_exists_relHypAt`
  turns that into an `X` carrying its own hyperbolicity certificate;
* the design's `geodesic` field is no longer spent.  `HasGeodesicSpellings` is a
  theorem for `relLengthOf X` (`hasGeodesicSpellings_relLengthOf`), so the leaf
  does not ask for it;
* the leaf's letters clause is membership in the alphabet `X ⊔ ℋ`, which
  `mem_alphabet_of_relLengthOf_le_one` derives from the design's own
  `relators_letters`.

Everything else -- `finitelyPresented`, `partnerHom_surjective`,
`ambient_torsionFree`, `fragmentSlack`, `factorMap_source_injective`,
`isPowerTorsionFree_of_torsionLifts` -- is reused unchanged, and none of it
spends a leaf.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric

/-! ## 1.  The design, over the relative Cayley graph -/

/-- **Fournier-Facio's Proposition 2.3, at the relative Cayley graph.**

One relative generating set `X` for the pair `(U ∗ H, U)`, certified hyperbolic
at that very `X`, and then a router design for **every** length demand `rho`,
whose relators are geodesic words of `X ⊔ ℋ` and satisfy Osin's `C'(1/7)` over
group pieces.

The `∀ rho` is what the leaf's `∃ rho` forces, and it is the clause an
elementary partner cannot meet: with `X` finite and the partner abelian, a tie
relator is a source letter followed by a geodesic word of the partner, such
words are periodic, and the rotations of one relator then share a prefix of
length `|r| - O(1)`, which `LetterMetricGroupSmallCancellation` at `1/7`
forbids.  A non-elementary `H` meets it, because a free pair inside `H` supplies
arbitrarily long words in general position over one finite generating set.
`IsNonElementaryHyperbolic H` is therefore load-bearing here, and this is the
first generation in which that reasoning is available: it needs the alphabet to
be fixed and finite, which is exactly what the earlier leaves did not say. -/
def OsinRelatorDesignCayley : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    Group.IsFinitelyPresented U → IsPowerTorsionFree U →
      Infinite H → Group.IsFinitelyPresented H → IsPowerTorsionFree H →
        IsNonElementaryHyperbolic H →
          IsRelativelyHyperbolic (CoprodI (pairFamily U H))
              (fun _ : Unit => freeProductPeripheral U H) →
            ∃ X : RelativeGeneratingSet (CoprodI (pairFamily U H))
                (fun _ : Unit => sourceFactor (pairFamily U H)),
              IsRelHypAt X ∧ ∀ rho : ℕ,
                ∃ D : WeightedRouterDesign U H (pairFamily U H),
                  D.relLength = relLengthOf X ∧
                    (∀ r ∈ D.relators, rho ≤ r.length) ∧
                    (∀ r ∈ D.relators, LetterGeodesic D.relLength r) ∧
                    LetterMetricGroupSmallCancellation D.relators (1 / 7)

/-! ## 2.  The composition -/

/-- **The small-cancellation quotient, over the fourth-generation conditions.**

Two leaf applications, at the same relator family: the Greendlinger bound gives
the embedding of the source through `factorMap_source_injective`, and the
torsion clause gives torsion-freeness of the quotient through
`isPowerTorsionFree_of_torsionLifts`.  Everything else is a field of the design
or a leaf-free theorem about it. -/
theorem exists_smallCancellationQuotient_cayley
    (hOsin : OsinTheorem24Cayley) (hDesign : OsinRelatorDesignCayley)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement)
    (U H : Type) [Group U] [Group H]
    (hUfp : Group.IsFinitelyPresented U) (hUtf : IsPowerTorsionFree U)
    (hHinf : Infinite H) (hHfp : Group.IsFinitelyPresented H)
    (hHtf : IsPowerTorsionFree H) (hHne : IsNonElementaryHyperbolic H) :
    ∃ (P : Type) (_ : Group P),
      Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
        (∃ p : H →* P, Function.Surjective p) ∧
        (∃ e : U →* P, Function.Injective e) := by
  haveI := hUfp
  haveI := hHfp
  have hrh : IsRelativelyHyperbolic (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
    hRelHyp U H inferInstance inferInstance hHne.1
  obtain ⟨X, hX, hfam⟩ :=
    hDesign U H inferInstance inferInstance hUfp hUtf hHinf hHfp hHtf hHne hrh
  obtain ⟨rho, hleaf⟩ := hOsin (pairFamily U H) inferInstance X hX (1 / 7)
  obtain ⟨D, hLeq, hlong, hgeo, hgp⟩ := hfam rho
  obtain ⟨hleafG, hleafT⟩ := hleaf D.relators
  rw [hLeq] at hgeo
  have hred : ∀ r ∈ D.relators, LetterReduced (relLengthOf X) r := by
    rw [← hLeq]
    exact D.relators_cyclicallyReduced
  have hlet : ∀ r ∈ D.relators, ∀ a ∈ r, a ∈ X.alphabet.carrier := by
    intro r hr a ha
    refine mem_alphabet_of_relLengthOf_le_one X ?_
    rw [← hLeq]
    exact D.relators_letters r hr a ha
  have hfloor : ∀ r ∈ D.relators, 4 ≤ r.length := by
    intro r hr
    have h := D.relators_long r hr
    omega
  have hbound : RelativeLengthBound (relLengthOf X) D.relators :=
    hleafG D.relators_symmetrized hred hlet hgeo hlong D.fragmentSlack hgp
  have hemb : Function.Injective D.emb :=
    (factorMap_source_injective hbound hfloor).comp D.sourceEquiv.injective
  have htors : IsPowerTorsionFree D.Routed :=
    isPowerTorsionFree_of_torsionLifts (D.ambient_torsionFree hUtf hHtf)
      (hleafT D.relators_symmetrized hred hlet hgeo hlong D.fragmentSlack hgp
        D.relators_noProperPower)
  exact ⟨D.Routed, inferInstance, D.finitelyPresented, htors,
    ⟨D.partnerHom, D.partnerHom_surjective⟩, ⟨D.emb, hemb⟩⟩

/-! ## 3.  The endpoint -/

/-- **`FournierFacioQuotientStatement` from the fourth-generation inputs.**

Three named `Prop`s, as in every generation.  What has changed is that the first
is Osin's theorem at the object Osin states it over -- a finite relative
generating set of a relatively hyperbolic pair -- so the chain no longer rests
on a hypothesis this repository has refuted.  The property-`(T)` hypothesis is
still spent on non-elementarity of `H₀`, through
`isNonElementaryHyperbolic_of_kazhdan'`. -/
theorem fournierFacioQuotientStatement_of_osin_cayley
    (hOsin : OsinTheorem24Cayley) (hDesign : OsinRelatorDesignCayley)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient_cayley hOsin hDesign hRelHyp U H₀
    hUfp hUtf hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan' hhyp hT)

end RelHyp
end GGT
end GroupApproximation
