import GroupApproximation.GGT.HullSCLemma44QuasiGeodesicBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The non-quasi-geodesic branch of Osin's Lemma 5.1, and where it does not help

`HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement`
(`GGT/HullSCLemma44QuasiGeodesicBridge.lean`) is Osin's Lemma 5.1 with the
certificate hypothesis restricted to the diagrams his Lemma 4.4 applies to, and
it is one of the four open leaves of Theorem C.  Its proof opens *"Suppose first
that `p` is not `(1/2,0)`-quasi-geodesic"*.  The bridge file isolates that split
— `hasQuasiGeodesicSpelling_or_notQuasiGeodesicSpelling` — and says of the
second alternative that it *"mentions no diagram, no relator and no quotient,
which is what lets a metric shortcut consume it"*.

## The metric shortcut is already in the tree

`GGT/VanKampen/GeodesicQuasiGeodesic.lean` proves
`exists_geodesicWord_isLambdaCQuasiGeodesicWord`: **every** element of the group
is spelled by a geodesic word, and a geodesic word is `(lambda,c)`-quasi-geodesic
for every `lambda ≤ 1` and `c ≥ 0`.  So the word-level branch costs nothing at
all, and the two theorems below are short consequences of it rather than new
mathematics.  Recording that is the point: anyone reading the bridge's header
would expect the missing work to be the shortcut, and it is not.

## Where the leaf actually stands

`RelativeDehnCut D W eps q boundaryWord` names a relator with a long contiguity
**along `boundaryWord` itself**, and `RelativeDehnTransferAt` asks for such a cut
at *every* word of the kernel.  A shorter spelling of the same element is
therefore not yet a cut for the original word: Osin's induction transports the
filling back along the replacement, and that transport is what the repository
does not have.  The obstruction is the transport, not the shortcut.

So this file is a navigational result plus two small theorems, and it does not
close the leaf.  Nothing here claims otherwise.

## What is proved

* `exists_shorter_admissible_of_not_quasiGeodesic` — an admissible word that
  fails to be `(1/4,1)`-quasi-geodesic is strictly longer than a geodesic word
  for the same element, so the same element has a strictly shorter admissible
  spelling.  The strictness is the whole content: a word of geodesic length
  *is* geodesic, hence quasi-geodesic, contradicting the hypothesis.
* `exists_shorter_spelling_of_not_hasQuasiGeodesicSpelling` — the same at a
  reduced diagram, so that both halves of the bridge's case split are available
  in usable form.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u w

/-! ## The shortening step -/

/-- **A failure of quasi-geodesicity is a strictly shorter spelling.**

A geodesic word for `RelLetter.listVal outer` has length
`wordDist D.alphabet.carrier 1 (listVal outer)`, which
`RelativeBoundaryContiguity.wordNorm_listVal_le_length` bounds by
`outer.length`.  Equality would make `outer` itself a geodesic word, and
`isLambdaCQuasiGeodesicWord_quarter_one_of_isGeodesicWord` would then make it
`(1/4,1)`-quasi-geodesic, against the hypothesis.  So the inequality is
strict. -/
theorem exists_shorter_admissible_of_not_quasiGeodesic
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {outer : List (GGT.RelLetter G Lambda)}
    (hadm : RelWord.IsAdmissible D outer)
    (hnot : ¬ GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 outer) :
    ∃ outer' : List (GGT.RelLetter G Lambda),
      RelWord.IsAdmissible D outer' ∧
        GGT.RelLetter.listVal outer' = GGT.RelLetter.listVal outer ∧
          outer'.length < outer.length := by
  obtain ⟨w, hw⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 (GGT.RelLetter.listVal outer)
  have hle : w.length ≤ outer.length := by
    rw [hw.2.2, WordMetric.wordDist_one_left]
    exact RelativeBoundaryContiguity.wordNorm_listVal_le_length D outer hadm
  refine ⟨w, hw.1, by simpa using hw.2.1, ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (isLambdaCQuasiGeodesicWord_quarter_one_of_isGeodesicWord D
      (show GGT.OsinComponents.IsGeodesicWord D 1
          (GGT.RelLetter.listVal outer) outer from
        ⟨hadm, one_mul _, by rw [← heq]; exact hw.2.2⟩)) hnot

/-! ## The branch at a reduced diagram -/

/-- **The second alternative of the bridge's case split, in usable form.**

Either the diagram carries the restricted certificate's hypothesis, or the
element its designated boundary word spells has a strictly shorter admissible
spelling — a statement with no diagram, no relator and no quotient in it. -/
theorem exists_shorter_spelling_of_not_hasQuasiGeodesicSpelling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R) (h : ¬ Z.HasQuasiGeodesicSpelling) :
    ∃ outer' : List (GGT.RelLetter G Lambda),
      RelWord.IsAdmissible D outer' ∧
        GGT.RelLetter.listVal outer' = Z.boundaryWord.prod ∧
          outer'.length < Z.boundaryWord.length := by
  rcases hasQuasiGeodesicSpelling_or_notQuasiGeodesicSpelling Z with hq | hbad
  · exact absurd hq h
  · obtain ⟨outer, hadm, hmap, hnot⟩ := hbad
    obtain ⟨outer', hadm', hval', hlen'⟩ :=
      exists_shorter_admissible_of_not_quasiGeodesic D hadm hnot
    refine ⟨outer', hadm', ?_, ?_⟩
    · rw [hval', listVal_of_letterwise_spelling hmap]
    · rw [← length_of_letterwise_spelling hmap]
      exact hlen'

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.exists_shorter_admissible_of_not_quasiGeodesic
#audit_axioms GroupApproximation.HullSC.exists_shorter_spelling_of_not_hasQuasiGeodesicSpelling
