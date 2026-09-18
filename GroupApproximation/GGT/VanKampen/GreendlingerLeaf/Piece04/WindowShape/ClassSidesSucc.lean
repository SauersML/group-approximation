import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: adjacent sides of a class are successive mod `sideCount`

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-02`, step 2 of the
argument in `Piece04.RotationTurns` ("Consecutive class sides `s`, `s+1` are consecutive on `∂Γ`
(`sides_eq`)").

*Statement.*  For a class `i < Q.classCount k`, every side of the class is a side of the polygon,
and two adjacent entries `s`, `s'` of `Q.classSides k i` satisfy `s' = (s + 1) % P.sideCount k`.

*Truth check.*  Write `m = P.sideCount k`, `b = Q.classBase k`, `L = (List.range m).rotate b`.
By `sides_eq`, `L` is the concatenation of the class side lists, so `classSides k i` is a
contiguous block (an infix) of `L`.  By `List.getElem_rotate`, `L[p] = (p + b) % m`, so
`L[p + 1] = (L[p] + 1) % m` for every `p + 1 < m`.  Adjacent entries of an infix are adjacent
entries of `L`.  This holds whatever `m` is: if the class has two entries then `m ≥ 2`.

*Proof route.*  `OsinLemma94RealizedPolygons.range_flatMap_eq_split` exhibits the infix,
`CyclicRuns.isChain_rotate_range` gives the chain on `L`, `List.IsChain.infix` restricts it, and
`List.IsChain.getElem` extracts the pair.  Membership in the polygon is
`OsinLemma94ClassPolygons.lt_sideCount_of_mem`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- The sides of a class are an infix of the sides read cyclically from `classBase k`. -/
theorem classSides_infix {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (hi : i < Q.classCount k) :
    Q.classSides k i <:+: (List.range (P.sideCount k)).rotate (Q.classBase k) := by
  rw [← Q.sides_eq k, OsinLemma94RealizedPolygons.range_flatMap_eq_split (Q.classSides k) hi]
  exact ⟨_, _, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc.classSides_infix

/-- The sides of a class form a chain of successive sides mod `sideCount`. -/
theorem classSides_isChain {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (hi : i < Q.classCount k) :
    (Q.classSides k i).IsChain fun s s' => s' = (s + 1) % P.sideCount k :=
  (CyclicRuns.isChain_rotate_range (P.sideCount k) (Q.classBase k)).infix
    (classSides_infix Q k i hi)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc.classSides_isChain

/-- **Adjacent sides of a class are successive mod `sideCount`** (lane `gl-p04-02`).  Every side
of class `i` is a side of polygon `k`, and adjacent entries `s`, `s'` of the class side list
satisfy `s' = (s + 1) % P.sideCount k`. -/
theorem succ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (hi : i < Q.classCount k) :
    (∀ s ∈ Q.classSides k i, s < P.sideCount k) ∧
      ∀ (n s s' : ℕ), (Q.classSides k i)[n]? = some s →
        (Q.classSides k i)[n + 1]? = some s' → s' = (s + 1) % P.sideCount k := by
  refine ⟨fun s hs => Q.lt_sideCount_of_mem k i hi s hs, ?_⟩
  intro n s s' hs hs'
  obtain ⟨hn1, hgs'⟩ := List.getElem?_eq_some_iff.mp hs'
  obtain ⟨_, hgs⟩ := List.getElem?_eq_some_iff.mp hs
  have h := (classSides_isChain Q k i hi).getElem n hn1
  subst hgs hgs'
  exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc.succ

/-- Lane `gl-p04-02` as a statement, for the assembly lane. -/
def ClassSidesSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ), i < Q.classCount k →
      (∀ s ∈ Q.classSides k i, s < P.sideCount k) ∧
        ∀ (n s s' : ℕ), (Q.classSides k i)[n]? = some s →
          (Q.classSides k i)[n + 1]? = some s' → s' = (s + 1) % P.sideCount k

/-- Lane `gl-p04-02`, closed. -/
theorem statement : ClassSidesSuccStatement.{u, w, v} :=
  fun Q k i hi => succ Q k i hi

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc.statement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc
