import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.Meta.AxiomGuard

/-!
# Inserting a word that separates a path from its reverse

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  In Case 2 the target side of a backwards connector pair lies on a cutting path, and
the target segment is longer than `ε`.  The walk across the segment runs back along it, so its
reverse darts lie on the same `G`-face, on one of the two stretches of the walk between the
source and target segments.  The connector ending on that stretch is inserted across the face.
The face splits in two, with the target segment on one side and its reverse on the other.
Removing the segment (`SeparatingPathRemovalInput`) takes away more darts than the insertion
added, against `GloballyDistinguishedSectionFamily.DartMinimal`.

`SeparatedCornerInsertionInput` is the insertion.  The walk of an unselected `G`-face reads
`front ++ back` from some base, and `word` has the value of `front`.  A segment of `back` whose
reverse darts lie in `front` runs, after the insertion, between two different unselected
`G`-faces.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

/-- **Inserting a word that separates a path from its reverse.**  Let `f` be an unselected
`G`-face whose walk, from some base, reads `front ++ back` with `back` nonempty.  Let `path` be a
segment of `back` whose reverse darts lie in `front`, with the walk across `path` running back
along it.  Let `word` be a nonempty legal word with the value of `front`.  Inserting `word`
across `f`, from the corner before `front` to the corner after it, gives an optimal family with
the same unbound sum and at most `2 |word|` more darts.  In it the transported `path` has no edge
twice, has inner vertices of valence two, and runs between two different unselected
`G`-faces. -/
def SeparatedCornerInsertionInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (r : ℕ) (front back path : List S.diagram.toCombMap.Dart)
    (word : List (RelLetter G Lambda)),
    S.UnselectedGFace f →
    (S.diagram.faceBoundary f).darts.rotate r = front ++ back → back ≠ [] →
    path <:+: back →
    (∀ d ∈ path, S.diagram.toCombMap.alpha d ∈ front) →
    S.RunsBackAcross path →
    word ≠ [] → HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) word →
    RelLetter.listVal word = RelLetter.listVal (dartWord S.diagram front) →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.unboundSum = S.unboundSum ∧
        T.diagram.toCombMap.dartCount ≤ S.diagram.toCombMap.dartCount + 2 * word.length ∧
        ∃ path' : List T.diagram.toCombMap.Dart, path'.length = path.length ∧ path'.Nodup ∧
          T.DegreeTwoJoints path' ∧
          ∃ first second : T.diagram.toCombMap.Face, first ≠ second ∧
            T.UnselectedGFace first ∧ T.UnselectedGFace second ∧
            ∀ d ∈ path', T.diagram.toCombMap.faceOf d = first ∧
              T.diagram.toCombMap.faceOf (T.diagram.toCombMap.alpha d) = second

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen
