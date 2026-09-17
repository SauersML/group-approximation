import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjointPosition
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: class darts of distinct cell classes are disjoint

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This is lane `gl-p04-11`.  Let
`Γ = P.face k`, and let `i ≠ i'` be two classes of polygon `k`, both of kind `cell j`.  Then
`classDarts k i` and `classDarts k i'` have no common dart.

## Proof

Suppose `x` sits at position `n` of class `i` and at position `n'` of class `i'`.  Every class dart
is a side dart of its class, or a gap dart of its class that is not the last class dart
(`side_or_gap_succ`, module `Piece04.WindowShape.ClassDisjointPosition`).

1. *Side and side.*  `x ∈ side s`, `x ∈ side s'` with `s` in class `i` and `s'` in class `i'`.
   Then `s ≠ s'` (`classSides_disjoint`), and different sides share no dart
   (`OsinLemma94RealizedPolygons.sideDarts_disjoint`).
2. *Side and gap.*  A side dart lies on `Γ` (`faceOf_of_mem_sideDarts`), and a gap dart of a cell
   class lies off `Γ` (`GapOffFaceStatement`, lane `gl-p04-10`).
3. *Gap and gap.*  Both positions have successors `e`, `e'`.  By the class step
   (`ClassStep.sigma_succ`, lane `gl-p04-01`), `σ e = α x = σ e'`, and `σ` is injective, so
   `e = e'` sits at positions `n + 1` and `n' + 1`.

Case 3 moves one step forward in class `i`.  The induction is on a bound `m` with
`length (classDarts k i) ≤ n + m`.  At `m = 0` position `n` does not exist.

## Interfaces

* Lane `gl-p04-01` is on disk: `ClassStep.sigma_succ` is imported and used directly.
* Lane `gl-p04-08` is not needed: the library lemma `OsinLemma94RealizedPolygons.sideDarts_disjoint`
  (module `Estimating.OsinLemma94ShortSides`) gives disjointness of different sides.
* Lane `gl-p04-10` is not on disk.  `GapOffFaceStatement` states its target verbatim, and the
  endpoint `disjoint_of_gapOffFace` is the reduction.  This statement is true (cartographer truth
  check T6, planar pinch loop).  It is strictly weaker than the target of this lane in proof
  content: it concerns gaps only, not all class darts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint

universe u w v

/-- **Gap darts of a cell class are off the polygon face** (lane `gl-p04-10`, not yet on disk).
For a class of kind `cell j`, every dart in the gap after a side of the class lies on a face other
than `P.face k`. -/
def GapOffFaceStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount),
    i < Q.classCount k → Q.classKind k i = .cell j →
    ∀ s ∈ Q.classSides k i, ∀ g ∈ Q.gap k s, S.diagram.toCombMap.faceOf g ≠ P.face k

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.GapOffFaceStatement

/-- **Class darts of distinct classes are disjoint** (lane `gl-p04-11`).  Two distinct classes of
polygon `k` of the same relator-cell kind have no common class dart. -/
def ClassDisjointStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i i' : ℕ) (j : Fin S.diagram.rCellCount),
    i < Q.classCount k → i' < Q.classCount k → i ≠ i' →
    Q.classKind k i = .cell j → Q.classKind k i' = .cell j →
    List.Disjoint (Q.classDarts k i) (Q.classDarts k i')

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.ClassDisjointStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **No common dart, by induction forward along class `i`.**  If `x` sits at position `n` of
class `i` and at position `n'` of class `i'`, and `length (classDarts k i) ≤ n + m`, then we reach
a contradiction.  Cases: side/side, side/gap, gap/side, and gap/gap, which steps to `n + 1`. -/
theorem false_of_getElem? (hgap : GapOffFaceStatement.{u, w, v})
    (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) {i i' : ℕ} {j : Fin S.diagram.rCellCount}
    (hi : i < Q.classCount k) (hi' : i' < Q.classCount k) (hii' : i ≠ i')
    (hk : Q.classKind k i = .cell j) (hk' : Q.classKind k i' = .cell j) :
    ∀ (m n n' : ℕ) (x : S.diagram.toCombMap.Dart), (Q.classDarts k i).length ≤ n + m →
      (Q.classDarts k i)[n]? = some x → (Q.classDarts k i')[n']? = some x → False := by
  intro m
  induction m with
  | zero =>
    intro n n' x hlen hx _
    obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.mp hx
    omega
  | succ m ih =>
    intro n n' x hlen hx hx'
    rcases side_or_gap_succ Q k hi hx with ⟨s, hs, hxs⟩ | ⟨⟨s, hs, hxg⟩, hsucc⟩
    · rcases side_or_gap_succ Q k hi' hx' with ⟨s', hs', hxs'⟩ | ⟨⟨s', hs', hxg'⟩, -⟩
      · have hne : s ≠ s' := fun h => Q.classSides_disjoint k hi hi' hii' hs (h ▸ hs')
        exact P.sideDarts_disjoint k (Q.lt_sideCount_of_mem k i hi s hs)
          (Q.lt_sideCount_of_mem k i' hi' s' hs') hne hxs hxs'
      · exact hgap Q k i' j hi' hk' s' hs' x hxg'
          (faceOf_of_mem_sideDarts (Q.lt_sideCount_of_mem k i hi s hs) hxs)
    · rcases side_or_gap_succ Q k hi' hx' with ⟨s', hs', hxs'⟩ | ⟨-, hsucc'⟩
      · exact hgap Q k i j hi hk s hs x hxg
          (faceOf_of_mem_sideDarts (Q.lt_sideCount_of_mem k i' hi' s' hs') hxs')
      · obtain ⟨e, he⟩ : ∃ e, (Q.classDarts k i)[n + 1]? = some e :=
          ⟨_, List.getElem?_eq_getElem hsucc⟩
        obtain ⟨e', he'⟩ : ∃ e', (Q.classDarts k i')[n' + 1]? = some e' :=
          ⟨_, List.getElem?_eq_getElem hsucc'⟩
        have heq : e = e' := Equiv.injective S.diagram.toCombMap.sigma
          ((ClassStep.sigma_succ Q k i j hi hk n x e hx he).trans
            (ClassStep.sigma_succ Q k i' j hi' hk' n' x e' hx' he').symm)
        subst heq
        exact ih (n + 1) (n' + 1) e (by omega) he he'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.false_of_getElem?

/-- **Class darts of distinct cell classes are disjoint, from lane `gl-p04-10`** (endpoint of lane
`gl-p04-11`). -/
theorem disjoint_of_gapOffFace (hgap : GapOffFaceStatement.{u, w, v}) :
    ClassDisjointStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k i i' j hi hi' hii' hk hk' x hx hx'
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hx
  obtain ⟨n', hn'⟩ := List.getElem?_of_mem hx'
  exact false_of_getElem? hgap Q k hi hi' hii' hk hk' (Q.classDarts k i).length n n' x
    (Nat.le_add_left _ _) hn hn'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.disjoint_of_gapOffFace

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint
