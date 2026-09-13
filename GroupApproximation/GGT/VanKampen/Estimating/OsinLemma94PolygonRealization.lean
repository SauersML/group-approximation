import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94DartMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# Realizing the component polygons of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4: each component is cut "along `t_1, …, t_l`" into a
polygon.  `OsinLemma94PolygonRealizationInput` asks for these polygons on the unselected
`G`-faces of an optimal family with the fewest darts.  This file splits it into four pieces.

* `OsinLemma94CuttingChainsInput`: with the fewest darts, the cutting chains are
  `(λ, c + 2)`-quasi-geodesic.  "This contradicts our assumption that `∑ l(t_i)` is minimal."
  It comes from `ChainRespellInput`, `PendantPathRemovalInput` and the word-metric fact
  `QuasiGeodesicRespellInput`.
* `OsinLemma94CellArcsInput`: arcs of relator cells are quasi-geodesic, from the `C`-condition.
* `OsinLemma94BoundaryArcsInput`: arcs of `∂Δ` inside one section are quasi-geodesic.
* `OsinLemma94PolygonPartitionInput`: the walk of every unselected `G`-face splits into maximal
  sides, once no two different unselected `G`-faces share an edge and the three kinds of long
  arcs are quasi-geodesic.

`GloballyDistinguishedSectionFamily.gFacesApart_of_dartMinimal` proves that two different
unselected `G`-faces share no edge: a `G`-face merge would remove two darts.
`osinLemma94PolygonRealizationInput_of_pieces` is the assembly.
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

/-- **No two different unselected `G`-faces share an edge.** -/
def GFacesApart (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∀ d : S.diagram.toCombMap.Dart, S.UnselectedGFace (S.diagram.toCombMap.faceOf d) →
    S.UnselectedGFace (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) →
      S.diagram.toCombMap.faceOf d = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)

/-- **The relator arcs are quasi-geodesic.**  Every arc of a relator cell, read from across, is
`(λ, c + 2)`-quasi-geodesic over the symmetric label alphabet. -/
def CellArcsQuasiGeodesic (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    Prop :=
  ∀ (j : Fin S.diagram.rCellCount) (arc : CyclicArc (cellDarts S.diagram j)),
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
      (dartWord S.diagram arc.reverseDarts)

/-- **The boundary arcs are quasi-geodesic.**  Every arc of `∂Δ` inside section `j` is
`(λ, c + 2)`-quasi-geodesic over the symmetric label alphabet. -/
def BoundaryArcsQuasiGeodesic
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∀ (j : ℕ) (hj : j < cuts.count) (arc : CyclicArc (targetDarts S.diagram none)),
    cuts.cut ⟨j, by omega⟩ ≤ arc.start.1 →
    arc.start.1 + arc.length ≤ cuts.cut ⟨j + 1, by omega⟩ →
      IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
        (dartWord S.diagram arc.darts)

/-- **The cutting chains are quasi-geodesic.**  A chain of darts on the walk of an unselected
`G`-face, with this face across every dart and the walk across running back along it, is
`(λ, c + 2)`-quasi-geodesic over the symmetric label alphabet. -/
def CuttingChainsQuasiGeodesic
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∀ (f : S.diagram.toCombMap.Face) (r : ℕ) (chain rest : List S.diagram.toCombMap.Dart),
    S.UnselectedGFace f → (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest →
    (∀ d ∈ chain, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f) →
    S.RunsBackAcross chain →
      IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
        (dartWord S.diagram chain)

/-- **Two different unselected `G`-faces share no edge** in a family with the fewest darts.
A `G`-face merge across the edge removes two darts and keeps the unbound sum. -/
theorem gFacesApart_of_dartMinimal
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal) :
    S.GFacesApart := by
  intro d hfirst hsecond
  by_contra hne
  obtain ⟨R, rfl⟩ : ∃ R : Surgery.GFaceMerge S.diagram, R.dart = d :=
    ⟨⟨d, hne, hfirst.1, hsecond.1, fun C hC => ⟨hfirst.2.1 C hC, hsecond.2.1 C hC⟩⟩, rfl⟩
  have havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 := fun b hb =>
    ⟨hfirst.2.2 b hb, hsecond.2.2 b hb⟩
  have hle := hS (Surgery.GFaceMerge.transportDistinguished S R havoid)
    (Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R havoid)
  have htwo := Surgery.GFaceMerge.transportDistinguished_dartCount_add_two S R havoid
  omega

end GloballyDistinguishedSectionFamily

/-- **Respelling a word that is not quasi-geodesic.**  Let `word` be legal over the symmetric
label alphabet and not `(λ, c + 2)`-quasi-geodesic, with `λ ≤ 1` and `0 ≤ c`.  Then some
subword `(word.drop i).take n` has a strictly shorter nonempty legal spelling.  If the endpoints
of a violating subword differ, a geodesic spelling is shorter.  Otherwise the subword has at
least three letters, and without its last letter it is spelled by the inverse of that letter. -/
def QuasiGeodesicRespellInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ),
    lambda ≤ 1 → 0 ≤ c → ∀ word : List (RelLetter G Lambda),
      HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) word →
      ¬ IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2) word →
        ∃ i n : ℕ, i + n ≤ word.length ∧ ∃ respelling : List (RelLetter G Lambda),
          respelling ≠ [] ∧ respelling.length < n ∧
            HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) respelling ∧
            RelLetter.listVal respelling = RelLetter.listVal ((word.drop i).take n)

/-- **Cutting chains piece of Lemma 9.4.**  "This contradicts our assumption that `∑ l(t_i)` is
minimal."  With the fewest darts, the cutting chains are `(λ, c + 2)`-quasi-geodesic. -/
def OsinLemma94CuttingChainsInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    lambda ≤ 1 → 0 ≤ c → S.DartMinimal → S.CuttingChainsQuasiGeodesic

/-- **Relator arcs piece of Lemma 9.4.**  Under the `C`-condition every arc of a relator cell is
quasi-geodesic: the words of `W` are `(λ, c)`-quasi-geodesic and closed under cyclic shifts. -/
def OsinLemma94CellArcsInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) {mu : ℝ} {rho : ℕ},
    OsinCCondition D W eps mu lambda c rho → 0 ≤ c → S.CellArcsQuasiGeodesic

/-- **Boundary arcs piece of Lemma 9.4.**  Every arc of `∂Δ` inside one section is
quasi-geodesic, since each section is `(λ, c)`-quasi-geodesic. -/
def OsinLemma94BoundaryArcsInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    0 ≤ c → S.BoundaryArcsQuasiGeodesic

/-- **Partition piece of Lemma 9.4.**  Cut the walk of every unselected `G`-face into maximal
sides.  Across a dart lies the exterior (A2), a relator cell (A1), a selected region (A3), or
the face itself (a cutting path), since no other unselected `G`-face shares an edge with it.  A
side ends where the kind changes, where the walk across turns away, and at the ends of the
sections.  Runs along one selected region are cut into pieces of length `ε`. -/
def OsinLemma94PolygonPartitionInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    1 ≤ eps → S.GFacesApart → S.CellArcsQuasiGeodesic → S.BoundaryArcsQuasiGeodesic →
      S.CuttingChainsQuasiGeodesic → ∃ P : OsinLemma94RealizedPolygons S, P.Maximal

/-- **The realization piece of Lemma 9.4, from its four pieces.**  Take `ε₀ = ρ₀ = 1`. -/
theorem osinLemma94PolygonRealizationInput_of_pieces
    (hcutting : OsinLemma94CuttingChainsInput.{u, w, v})
    (hcells : OsinLemma94CellArcsInput.{u, w, v})
    (hboundary : OsinLemma94BoundaryArcsInput.{u, w, v})
    (hpartition : OsinLemma94PolygonPartitionInput.{u, w, v}) :
    OsinLemma94PolygonRealizationInput.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ hlambda hc _ _
  refine ⟨1, fun eps heps => ⟨1, Nat.one_pos, fun rho _ W hW Delta cuts _ _ S _ hS => ?_⟩⟩
  exact hpartition S heps (GloballyDistinguishedSectionFamily.gFacesApart_of_dartMinimal hS)
    (hcells S hW hc) (hboundary S hc) (hcutting S hlambda hc hS)

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.gFacesApart_of_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonRealizationInput_of_pieces

end GroupApproximation.GGT.VanKampen
