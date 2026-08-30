import GroupApproximation.GGT.RelHypOsinTheorem24Refuted
import GroupApproximation.GGT.RelHypKazhdanNonElementary
import GroupApproximation.GGT.RelHypAbelianPartnerNoGo

/-!
# The repaired weighted leaves, the repaired design, and the endpoint again

`GGT/RelHypOsinTheorem24Refuted.lean` refutes `OsinTheorem24` and names the two
defects: `WeightedGreendlingerLeaf` never asks its relators to be **geodesic**
words, and `LetterIsPiece` is a **syntactic** common prefix where Osin's pieces
are subwords equal *in the group*.  This module carries the repair through to
`FournierFacioQuotientStatement`.

## RETIRED from hypothesis position (issue #52)

`OsinTheorem24Repaired` is refuted by `GGT/RelHypOsin24Collapse.
not_osinTheorem24Repaired`, and the two further generations built on it -- the
final form here and the Cayley form of `GGT/RelHypOsin24CayleyLeaf.lean` -- are
retired as well.  The head of the chain,
`GGT/RelHypOsinTheorem24.lean`, carries the explanation; in one sentence,
**Osin's Theorem 2.4 has no small-cancellation hypothesis in it**, so every
generation of this chain transcribed §4's machinery rather than the theorem, and
`OsinRelatorDesignRepaired` -- like its three siblings -- is a repository
artifact and not a statement anybody has made.

The route to `FournierFacioQuotientStatement` is now
`GGT/RelHypFournierFacioProp23.lean`.  This module stays as the record of the
repair that was attempted and of the abelian-partner obstruction, which remains
a true theorem about the object it names.

## Why the repair is a new module and not an edit

`Sofic/OsinWeightedMetric.lean` is in the root import closure and the two
defective leaves are consumed there by `WeightedRouterDesign.lengthBound`,
`emb_injective`, `torsionFree` and `kazhdanEnvelope_of_design`.  Editing the
leaves in place would break all four, and — more to the point — it would break
`not_osinTheorem24`, which is a theorem *about* the unrepaired leaf and which
should survive as the record of why the repair was needed.  A refutation whose
subject has been silently edited away is worth nothing.  So both statements
live: the original, still refuted, and the repaired one below.

The repaired composition is re-proved here from the design's own fields, so
nothing in the root closure has to move.  If the fleet later wants the repair
migrated into `Sofic/OsinWeightedMetric.lean`, the migration is mechanical and
`not_osinTheorem24` should be re-pointed at a preserved copy of the old leaf
rather than deleted.

## What changed in the leaves

Two hypotheses, in both `WeightedGreendlingerLeafRepaired` and
`WeightedTorsionLeafRepaired`:

* `∀ r ∈ R, LetterGeodesic L r` — each relator's letter count **is** the
  relative length of the element it spells.  This is what osin24's witness
  fails: a `42`-letter constant word over an alphabet containing `t^±42` spells
  a single letter.  Raising the length floor does not repair it, because the
  witness scales.
* `LetterMetricGroupSmallCancellation R lam` in place of
  `LetterMetricSmallCancellation R lam` — pieces compared in the group rather
  than syntactically.  `letterMetricSmallCancellation_of_group` shows the new
  condition is strictly stronger, so a design certifying the old one has *not*
  certified the new one and `WeightedRouterDesign.metric` cannot be reused.
  `OsinRelatorDesignRepaired` therefore carries the group-piece certificate as
  an extra clause alongside the design.

## The geodesicity clause costs undistortedness, and that is a reversal

`LetterGeodesic L r` is a **lower** bound on the alphabet-length of the element
`r` spells.  A design whose relators are words in a free pair `⟨a, b⟩ ≤ H` meets
it only if `⟨a, b⟩` is undistorted in the ambient generating set — otherwise a
shorter spelling exists outside the subgroup.  So
`PingPong.UndistortedPingPongFreeSubgroup`, which an earlier docstring of
`GGT/PingPongFreeSubgroup.lean` said not to prove, is exactly what this clause
needs.  That docstring is corrected.  The earlier reasoning was right about the
*piece* certificate and wrong to conclude anything about the design as a whole.

## The abelian-partner obstruction survives the repair

`not_weightedGreendlingerLeafRepaired_of_abelian_partner` below: a weighted
router design with a nonabelian source and an **abelian** partner refutes the
*repaired* leaf too, as soon as it meets the two new certificates.  The repair
addresses the geodesicity defect and the piece defect; it does not address this
one, because the obstruction never looks at pieces or at spellings — it observes
that the tie makes the partner surject, an abelian partner makes the quotient
abelian, and a dead source commutator is a relator-subgroup element of relative
length at most one.

So whoever proves the repaired leaf still owes an argument that no such design
exists, and the natural place for it is a **non-elementary partner** hypothesis,
which `OsinRelatorDesign` already carries and neither leaf does.  Checking that
before investing in the diagram argument is cheap; discovering it afterwards is
not.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinWeightedMetric

/-! ## 1.  The repaired leaves -/

/-- **The Greendlinger leaf, repaired**: relators geodesic, pieces compared in
the group. -/
def WeightedGreendlingerLeafRepaired {G : Bool → Type} [∀ b, Group (G b)]
    (L : RelativeLength G) (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  HasGeodesicSpellings L →
    LetterSymmetrized R → (∀ r ∈ R, LetterReduced L r) →
      (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
        (∀ r ∈ R, LetterGeodesic L r) →
          LetterFragmentSlack R lam →
            LetterMetricGroupSmallCancellation R lam →
              RelativeLengthBound L R

/-- **The torsion leaf, repaired**, with the same two changes. -/
def WeightedTorsionLeafRepaired {G : Bool → Type} [∀ b, Group (G b)]
    (L : RelativeLength G) (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  HasGeodesicSpellings L →
    LetterSymmetrized R → (∀ r ∈ R, LetterReduced L r) →
      (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
        (∀ r ∈ R, LetterGeodesic L r) →
          LetterFragmentSlack R lam →
            LetterMetricGroupSmallCancellation R lam →
              LetterNoProperPower R →
                TorsionLifts (letterRelatorSubgroup R)

/-- **Osin, Theorem 2.4(1) and 2.4(5), repaired.**  The universal closure of the
two repaired leaves.  Compare `OsinTheorem24`, which `not_osinTheorem24`
refutes. -/
def OsinTheorem24Repaired : Prop :=
  ∀ (G : Bool → Type) (_ : ∀ b, Group (G b)) (L : RelativeLength G)
    (R : Set (List (CoprodI G))) (lam : ℚ),
      WeightedGreendlingerLeafRepaired L R lam ∧ WeightedTorsionLeafRepaired L R lam

/-! ## 2.  The obstruction that the repair does not remove -/

/-- **An abelian partner refutes the repaired leaf as well.**

The two new certificates are hypotheses here, so this is not the claim that they
are unsatisfiable — it is the claim that satisfying them does not help.  The
obstruction never looks at spellings or at pieces: the tie makes the partner
surject, an abelian partner makes the quotient abelian, and a dead source
commutator is an element of the relator subgroup of relative length at most one,
which `not_relativeLengthBound_of_short` turns against the length floor.

The missing hypothesis is therefore a third one, about the partner factor, and
it is the one `OsinRelatorDesign` already carries: non-elementarity. -/
theorem not_weightedGreendlingerLeafRepaired_of_abelian_partner {U H : Type}
    [Group U] [Group H] {G : Bool → Type} [∀ b, Group (G b)]
    (D : WeightedRouterDesign U H G) (hH : ∀ p q : H, p * q = q * p)
    {x y : G false} (hxy : x * y ≠ y * x)
    (hgeo : ∀ r ∈ D.relators, LetterGeodesic D.relLength r)
    (hgp : LetterMetricGroupSmallCancellation D.relators (1 / 7)) :
    ¬ WeightedGreendlingerLeafRepaired D.relLength D.relators (1 / 7) := by
  intro hleaf
  exact not_relativeLengthBound_of_abelian_partner D hH hxy
    (hleaf D.geodesic D.relators_symmetrized D.relators_cyclicallyReduced
      D.relators_letters hgeo D.fragmentSlack hgp)

/-! ## 3.  The repaired design, and the composition re-proved -/

/-- **Fournier-Facio's Proposition 2.3, over the repaired conditions.**

The design is the same `WeightedRouterDesign`; what is added is the pair of
certificates the repaired leaves consume and `WeightedRouterDesign.metric` does
not supply.  Both are genuine new obligations on the relator family: geodesicity
needs the relators' subgroup undistorted, and the group-piece bound needs the
piece count to survive replacing syntactic equality of prefixes by equality in
the group. -/
def OsinRelatorDesignRepaired : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    Group.IsFinitelyPresented U → IsPowerTorsionFree U →
      Infinite H → Group.IsFinitelyPresented H → IsPowerTorsionFree H →
        IsNonElementaryHyperbolic H →
          IsRelativelyHyperbolic (CoprodI (pairFamily U H))
              (fun _ : Unit => freeProductPeripheral U H) →
            ∃ D : WeightedRouterDesign U H (pairFamily U H),
              (∀ r ∈ D.relators, LetterGeodesic D.relLength r) ∧
                LetterMetricGroupSmallCancellation D.relators (1 / 7)

/-- **The small-cancellation quotient, over the repaired conditions.**

The composition of `Sofic/OsinWeightedMetric.lean` is re-proved rather than
reused, because its `lengthBound`, `emb_injective` and `torsionFree` feed the
*unrepaired* leaves.  Every other ingredient is a field or a leaf-free theorem
of the design: `finitelyPresented`, `partnerHom_surjective`,
`ambient_torsionFree`, `fragmentSlack`, and the four relator certificates. -/
theorem exists_smallCancellationQuotient_repaired
    (hOsin : OsinTheorem24Repaired) (hDesign : OsinRelatorDesignRepaired)
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
  obtain ⟨D, hgeo, hgp⟩ :=
    hDesign U H inferInstance inferInstance hUfp hUtf hHinf hHfp hHtf hHne hrh
  obtain ⟨hleafG, hleafT⟩ :=
    hOsin (pairFamily U H) inferInstance D.relLength D.relators (1 / 7)
  have hfloor : ∀ r ∈ D.relators, 2 ≤ r.length := by
    intro r hr
    have h := D.relators_long r hr
    omega
  have hbound : RelativeLengthBound D.relLength D.relators :=
    hleafG D.geodesic D.relators_symmetrized D.relators_cyclicallyReduced
      D.relators_letters hgeo D.fragmentSlack hgp
  have hemb : Function.Injective D.emb :=
    (factorMap_source_injective hbound hfloor).comp D.sourceEquiv.injective
  have htors : IsPowerTorsionFree D.Routed :=
    isPowerTorsionFree_of_torsionLifts (D.ambient_torsionFree hUtf hHtf)
      (hleafT D.geodesic D.relators_symmetrized D.relators_cyclicallyReduced
        D.relators_letters hgeo D.fragmentSlack hgp D.relators_noProperPower)
  exact ⟨D.Routed, inferInstance, D.finitelyPresented, htors,
    ⟨D.partnerHom, D.partnerHom_surjective⟩, ⟨D.emb, hemb⟩⟩

/-! ## 4.  The endpoint, again -/

/-- **`FournierFacioQuotientStatement` from the repaired inputs.**

Three named `Prop`s, as before, and the middle one has grown two clauses.  The
property-`(T)` hypothesis is still spent on non-elementarity of `H₀`, through
`isNonElementaryHyperbolic_of_kazhdan'`, which needs no amenability. -/
theorem fournierFacioQuotientStatement_of_osin_repaired
    (hOsin : OsinTheorem24Repaired) (hDesign : OsinRelatorDesignRepaired)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient_repaired hOsin hDesign hRelHyp U H₀
    hUfp hUtf hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan' hhyp hT)

end RelHyp
end GGT
end GroupApproximation
