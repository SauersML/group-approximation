import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoinsCellArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: consecutive class darts of a cell class

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-01`, step 2 of the
argument in `Piece04.RotationTurns` ("consecutive class darts `c_i`, `c_(i+1)` satisfy
`φ (α c_(i+1)) = α c_i`, that is `σ c_(i+1) = α c_i`").

*Statement.*  Let class `i < Q.classCount k` have kind `cell j`.  If `d`, `e` are the entries at
positions `n`, `n + 1` of `Q.classDarts k i`, then `σ e = α d`.

*Truth check.*  By `cell_arc` the class darts are `arc.reverseDarts = (arc.darts.reverse).map α`
for one cyclic arc of the cell `Π = cell j`.  The arc darts follow the face permutation:
`φ a_(p-1) = a_p`.  Consecutive class darts are `c_n = α a_p` and `c_(n+1) = α a_(p-1)`, so
`σ c_(n+1) = σ (α a_(p-1)) = φ a_(p-1) = a_p = α c_n`.

*Proof route.*  `ClassProducer.isChain_backward_reverseDarts` with the `nonempty`, `chain` and
`closes` fields of the face boundary of the cell makes the class darts a
`ClassProducer.Backward` chain.  `List.IsChain.getElem` extracts the pair, and
`φ (α e) = σ (α (α e)) = σ e` by `CombMap.facePerm`, `Equiv.Perm.mul_apply` and
`alpha_involutive`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- The darts of a cell class are a backward walk across the cell. -/
theorem classDarts_isChain_backward {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (hi : i < Q.classCount k)
    (hj : Q.classKind k i = .cell j) :
    (Q.classDarts k i).IsChain (ClassProducer.Backward S.diagram.toCombMap) := by
  obtain ⟨arc, harc⟩ := Q.cell_arc k i j hi hj
  have hdarts : Q.classDarts k i = arc.reverseDarts := harc
  rw [hdarts]
  exact ClassProducer.isChain_backward_reverseDarts
    (S.diagram.faceBoundary (Embedded.cell S.diagram j).face).nonempty
    (S.diagram.faceBoundary (Embedded.cell S.diagram j).face).chain
    (S.diagram.faceBoundary (Embedded.cell S.diagram j).face).closes arc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep.classDarts_isChain_backward

/-- **Consecutive class darts of a cell class** (lane `gl-p04-01`).  If `d` and `e` sit at
positions `n` and `n + 1` of the darts of a class of kind `cell j`, then `σ e = α d`. -/
theorem sigma_succ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (hi : i < Q.classCount k)
    (hj : Q.classKind k i = .cell j) (n : ℕ) (d e : S.diagram.toCombMap.Dart)
    (hd : (Q.classDarts k i)[n]? = some d) (he : (Q.classDarts k i)[n + 1]? = some e) :
    S.diagram.toCombMap.sigma e = S.diagram.toCombMap.alpha d := by
  obtain ⟨hn1, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  have hstep := (classDarts_isChain_backward Q k i j hi hj).getElem n hn1
  unfold ClassProducer.Backward at hstep
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, S.diagram.toCombMap.alpha_involutive] at hstep
  exact hstep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep.sigma_succ

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep
