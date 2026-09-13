import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Respelling a cutting path of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  A cutting path of a component is a path of the optimal diagram with one unselected
`G`-face on both sides (`OsinLemma94RealizedPolygons`).  If a subpath has the value of a strictly
shorter legal word, replacing the subpath by that word gives an optimal family with the same
unbound sum and fewer darts, against `GloballyDistinguishedSectionFamily.DartMinimal`.  This is
why the cutting paths of a dart-minimal family are `(λ, c + 2)`-quasi-geodesic.

The replacement is three moves on the diagram, each carrying the family along.

* `CornerInsertionInput`: insert the word across the face, from the corner before the subpath to
  the corner after it.  The face splits in two, and the subpath now runs between the two halves.
* A `G`-face merge across the first edge of the subpath (`Surgery.GFaceMerge`).
* `PendantPathRemovalInput`: the rest of the subpath hangs from a vertex of valence one, and is
  removed.

`SeparatingPathRemovalInput` is the last two moves together, and `ChainRespellInput` is the
composite.  `chainRespellInput_of_pieces` derives it from the insertion and the removal.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- An unselected `G`-face: an inner face that is no relator cell and lies in no selected
region. -/
def UnselectedGFace (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) : Prop :=
  f ≠ S.diagram.outerFace ∧ (∀ C ∈ S.diagram.relatorCells, C.face ≠ f) ∧
    ∀ a ∈ S.family, f ∉ a.1

/-- The walk across the path runs back along it.  The field `cutting_interior` of
`OsinLemma94RealizedPolygons` has this form. -/
def RunsBackAcross (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (path : List S.diagram.toCombMap.Dart) : Prop :=
  ∀ (j : ℕ) (e e' : S.diagram.toCombMap.Dart), path[j]? = some e → path[j + 1]? = some e' →
    S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') = S.diagram.toCombMap.alpha e

/-- A path whose inner vertices have valence two: the walk runs along the path, and the walk
across it runs back along it. -/
def DegreeTwoJoints (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (path : List S.diagram.toCombMap.Dart) : Prop :=
  ∀ (j : ℕ) (e e' : S.diagram.toCombMap.Dart), path[j]? = some e → path[j + 1]? = some e' →
    S.diagram.toCombMap.facePerm e = e' ∧
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') = S.diagram.toCombMap.alpha e

/-- **Inserting a word across a `G`-face, from corner to corner.**  Let `f` be an unselected
`G`-face whose walk, from some base, reads `chain ++ rest`, where `chain` has `f` on both sides,
inner vertices of valence two, and no edge twice.  Let `word` be a nonempty legal word with the
value of `chain`.  Inserting `word` from the corner before `chain` to the corner after it gives
an optimal family with `2 |word|` more darts and the same unbound sum.  In it the transported
`chain` runs between two different unselected `G`-faces. -/
def CornerInsertionInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (r : ℕ) (chain rest : List S.diagram.toCombMap.Dart)
    (word : List (RelLetter G Lambda)),
    S.UnselectedGFace f →
    (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest → chain ≠ [] →
    (∀ d ∈ chain, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f) →
    (∀ d ∈ chain, S.diagram.toCombMap.alpha d ∉ chain) →
    S.RunsBackAcross chain →
    word ≠ [] → HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) word →
    RelLetter.listVal word = RelLetter.listVal (dartWord S.diagram chain) →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.unboundSum = S.unboundSum ∧
        T.diagram.toCombMap.dartCount = S.diagram.toCombMap.dartCount + 2 * word.length ∧
        ∃ path : List T.diagram.toCombMap.Dart, path.length = chain.length ∧ path.Nodup ∧
          T.DegreeTwoJoints path ∧
          ∃ first second : T.diagram.toCombMap.Face, first ≠ second ∧
            T.UnselectedGFace first ∧ T.UnselectedGFace second ∧
            ∀ d ∈ path, T.diagram.toCombMap.faceOf d = first ∧
              T.diagram.toCombMap.faceOf (T.diagram.toCombMap.alpha d) = second

/-- **Removing a pendant path from a `G`-face.**  Let `path` have an unselected `G`-face on both
sides, no edge twice, a first vertex of valence one, and inner vertices of valence two.  Removing
it gives an optimal family with `2 |path|` fewer darts and the same unbound sum. -/
def PendantPathRemovalInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (path : List S.diagram.toCombMap.Dart),
    S.UnselectedGFace f → path ≠ [] → path.Nodup →
    (∀ d ∈ path, S.diagram.toCombMap.alpha d ∉ path) →
    (∀ d ∈ path, S.diagram.toCombMap.faceOf d = f ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f) →
    (∀ d ∈ path.head?, S.diagram.toCombMap.sigma d = d) →
    S.DegreeTwoJoints path →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.unboundSum = S.unboundSum ∧
        T.diagram.toCombMap.dartCount + 2 * path.length = S.diagram.toCombMap.dartCount

/-- **Removing a path between two `G`-faces.**  Let `path` have inner vertices of valence two and
run between two different unselected `G`-faces.  Removing it merges the two faces and gives an
optimal family with `2 |path|` fewer darts and the same unbound sum.  A `G`-face merge removes
the first edge, and the rest is a pendant path. -/
def SeparatingPathRemovalInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (path : List S.diagram.toCombMap.Dart) (first second : S.diagram.toCombMap.Face),
    path ≠ [] → path.Nodup → first ≠ second →
    S.UnselectedGFace first → S.UnselectedGFace second → S.DegreeTwoJoints path →
    (∀ d ∈ path, S.diagram.toCombMap.faceOf d = first ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = second) →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.unboundSum = S.unboundSum ∧
        T.diagram.toCombMap.dartCount + 2 * path.length = S.diagram.toCombMap.dartCount

/-- **Respelling a cutting path.**  "This contradicts our assumption that `∑ l(t_i)` is
minimal."  Let `f` be an unselected `G`-face whose walk, from some base, reads `chain ++ rest`,
where `chain` has `f` on both sides, inner vertices of valence two, and no edge twice.  A
nonempty legal word with the value of `chain`, strictly shorter than `chain`, gives an optimal
family with the same unbound sum and fewer darts. -/
def ChainRespellInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (r : ℕ) (chain rest : List S.diagram.toCombMap.Dart)
    (word : List (RelLetter G Lambda)),
    S.UnselectedGFace f →
    (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest →
    (∀ d ∈ chain, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f) →
    (∀ d ∈ chain, S.diagram.toCombMap.alpha d ∉ chain) →
    S.RunsBackAcross chain →
    word ≠ [] → HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) word →
    RelLetter.listVal word = RelLetter.listVal (dartWord S.diagram chain) →
    word.length < chain.length →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.unboundSum = S.unboundSum ∧
        T.diagram.toCombMap.dartCount < S.diagram.toCombMap.dartCount

/-- **The respelling from the insertion and the removal.**  The insertion adds `2 |word|` darts
and the removal of the transported chain takes away `2 |chain|`. -/
theorem chainRespellInput_of_pieces (hinsert : CornerInsertionInput.{u, w, v})
    (hremove : SeparatingPathRemovalInput.{u, w, v}) : ChainRespellInput.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S f r chain rest word hf hwalk hacross hfree
    hjoints hne hword hvalue hlen
  have hchain : chain ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨T, hTsum, hTdarts, path, hpath, hnodup, hTjoints, first, second, hne12, hfirst,
    hsecond, hsides⟩ := hinsert S f r chain rest word hf hwalk hchain hacross hfree hjoints hne
      hword hvalue
  obtain ⟨U, hUsum, hUdarts⟩ := hremove T path first second
    (List.ne_nil_of_length_pos (by omega)) hnodup hne12 hfirst hsecond hTjoints hsides
  exact ⟨U, hUsum.trans hTsum, by omega⟩

end GloballyDistinguishedSectionFamily

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.chainRespellInput_of_pieces

end GroupApproximation.GGT.VanKampen
