import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, sub-leaf P07: the lake exclusion for the cell pocket walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The target is
`CellPocketWalkProperArcsBelowSectionStatement` (`Estimating/OsinPocketMultipleEdgeCopyBelow`): for
a cell pocket walk `K = s_1 t_1⁻¹ s_2 t_2⁻¹` between distinct cells `Π_i`, `Π_j` of the optimal copy
`X = S.diagram` of a least-area `Δ`, with `K` noncrossing and the exterior off its side, both arcs
are proper: `|t_1| < |∂Π_i|` and `|t_2| < |∂Π_j|`.  This module proves the **below form** directly
(it uses the inductive premise `OsinLemma97Below … Δ.rCellCount`), so `Piece07` takes the reduction
without `toBelow`.

## The mathematical proof

Thresholds: `ε₀ = 0`; `ρ₀ = max 2 ρ₁`, where `ρ₁` makes `λ⁻¹ (3ε + c) < (μ/2) ρ` for `ρ ≥ ρ₁`
(`SameCellSimplePocket.exists_rho_large`).  Each conjunct is `CyclicArc.length_le` plus the
exclusion of equality, so suppose `|t_1| = |∂Π_i|` or `|t_2| = |∂Π_j|`.

**Step 1 (lake filling).**  Say `t_1` is all of `∂Π_i`.  Every dart of `t_1⁻¹` is `α d` for a dart
`d` of `Π_i`, so the face across it is `Π_i`, which is off the side: the walk runs once around `Π_i`
with `Π_i` on the far side, and `Π_i` is a lake of the complement of `sideFaces K` (the model
`OsinPocketFullArcLakeModel`).  Let `F` be the side together with every lake, i.e. every face of the
complement not connected to the exterior across non-walk edges
(`Surgery.MapCollapse.ExteriorComponent.absorbed`).  The darts on the boundary of `F` are the walk
darts whose far face lies in the exterior component: all of `t_2⁻¹` when `Π_j` is exterior, none of
`t_1⁻¹`, and sub-lists `s_1' ⊆ s_1`, `s_2' ⊆ s_2`.  In the walk order they read
`s_1' s_2' t_2⁻¹` (or `s_1' s_2'` when `Π_j` is a lake too), and they turn to their successors
because the removed pieces are whole lake boundaries.  So `F` is an `EnclosedFaceSetSucc` with
`|s_1'|, |s_2'| ≤ ε` and the relator cell `Π_i ∈ F`.  Either some cell `Π_k` is off `F` (take the
arc `t_2` of `k = j`, or the empty arc of any off cell), or every relator cell lies in `F`.  This is
`LakeFillSuccStatement`.

**Step 2 (the cut, some cell off `F`).**  `enclosedLoopPocketRegionSucc_of_pieces` with the closed
doubling `enclosedBridgeDoublingSideArcSucc` and the closed unpinch `enclosedLoopPocketUnpinchSucc`
(every relator word is longer than one letter since `2 ≤ ρ ≤ |R|`) turns `F` into a pocket region
`P` of an O-equivalent copy `X'`, both cycles following their boundaries, with a relator cell inside,
a cell `i'` outside, `P⁻¹ = s' ++ A'⁻¹` and `dartWord s' = dartWord (s_1' ++ s_2')`.  Split `s'` at
`|s_1'|`: `dartWord` is a `List.map`, so the two halves read `s_1'` and `s_2'`, of norm at most their
lengths, at most `ε`.  With the empty arc of `i'` between them, `P⁻¹` reads
`s'₁ ∅⁻¹ s'₂ A'⁻¹`, and `nonempty_osinMultipleEdgeCut_of_pocketRegion` (closed collar, closed cell
transport) gives a multiple-edge cut of `Δ` with fewer relator cells.  Clause (b) below `Δ` and
`OsinMultipleEdgeCut.false_of_below` refute it (`false_of_enclosedSucc`).

**Step 3 (every relator cell in `F`).**  `F` is enclosed by a loop `s_1' s_2'` of length at most
`2ε` holding every relator cell.  This is `AllCellsShortLoopStatement`.

## Status

Closed here: steps 2 and the threshold wiring (`false_of_enclosedSucc`, `proof_of_gaps`).
Open, as named statements: step 1 (`LakeFillSuccStatement`; the corpus also leaves the walk order of
an absorbed boundary unproved, see `PocketFaceSet.absorb`) and step 3
(`AllCellsShortLoopStatement`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Lists

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The empty cyclic arc of a list. -/
def emptyArc {α : Type*} (l : List α) : CyclicArc l where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

/-- The empty arc reads no darts. -/
theorem emptyArc_darts {α : Type*} (l : List α) : (emptyArc l).darts = [] :=
  rfl

/-- The inverse of the empty arc reads no darts. -/
theorem invDarts_emptyArc {X : DiscDiagram.{u, w, v} W} (k : Fin X.rCellCount) :
    invDarts X (emptyArc (cellDarts X k)).darts = [] :=
  rfl

/-- **The first half of a split side reads the first side.** -/
theorem dartWord_take_of_eq {X X' : DiscDiagram.{u, w, v} W} {s' : List X'.toCombMap.Dart}
    {s₁ s₂ : List X.toCombMap.Dart} (h : dartWord X' s' = dartWord X (s₁ ++ s₂)) :
    dartWord X' (s'.take s₁.length) = dartWord X s₁ := by
  have hlen : (s₁.map X.label).length = s₁.length := List.length_map _
  unfold dartWord at h ⊢
  rw [List.map_take, h, List.map_append, List.take_left' hlen]

/-- **The second half of a split side reads the second side.** -/
theorem dartWord_drop_of_eq {X X' : DiscDiagram.{u, w, v} W} {s' : List X'.toCombMap.Dart}
    {s₁ s₂ : List X.toCombMap.Dart} (h : dartWord X' s' = dartWord X (s₁ ++ s₂)) :
    dartWord X' (s'.drop s₁.length) = dartWord X s₂ := by
  have hlen : (s₁.map X.label).length = s₁.length := List.length_map _
  unfold dartWord at h ⊢
  rw [List.map_drop, h, List.map_append, List.drop_left' hlen]

/-- The first half of a split side has norm at most `ε`. -/
theorem wordNorm_take_le {D : RelGenSet G Lambda} {eps : ℕ} {X X' : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {s' : List X'.toCombMap.Dart} {s₁ s₂ : List X.toCombMap.Dart}
    (hword : dartWord X' s' = dartWord X (s₁ ++ s₂)) (hs₁ : s₁.length ≤ eps) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' (s'.take s₁.length))) ≤ eps := by
  rw [dartWord_take_of_eq hword]
  exact (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁

/-- The second half of a split side has norm at most `ε`. -/
theorem wordNorm_drop_le {D : RelGenSet G Lambda} {eps : ℕ} {X X' : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {s' : List X'.toCombMap.Dart} {s₁ s₂ : List X.toCombMap.Dart}
    (hword : dartWord X' s' = dartWord X (s₁ ++ s₂)) (hs₂ : s₂.length ≤ eps) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' (s'.drop s₁.length))) ≤ eps := by
  rw [dartWord_drop_of_eq hword]
  exact (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂

/-- **A split side with the empty arc in the middle.**  `s' ++ A⁻¹` reads
`take ++ ∅⁻¹ ++ drop ++ A⁻¹`. -/
theorem split_decomposition {X : DiscDiagram.{u, w, v} W} (k : Fin X.rCellCount)
    {cycle s' tail : List X.toCombMap.Dart} (n : ℕ) (h : cycle = s' ++ tail) :
    cycle = s'.take n ++ invDarts X (emptyArc (cellDarts X k)).darts ++ s'.drop n ++ tail := by
  rw [h, invDarts_emptyArc, List.append_nil, List.take_append_drop]

end Lists

section Cut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **An enclosed face set read by two short sides and an arc is refuted below `Δ`.**  Take an
O-equivalent copy `X` of a least-area `Δ` with legal labels, and an enclosed face set of `X` turning
to its successors, with a relator cell inside and a cell `k` outside, whose inverse outside walk
reads `s_1 s_2` and an arc of `k` backwards, `|s_1|, |s_2| ≤ ε`.  Under `C(ε, μ, λ, c, ρ)` at the
thresholds, with clause (b) of Lemma 9.7 below `Δ`, this is impossible. -/
theorem false_of_enclosedSucc {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta X : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) (hCf : C.face ∈ faces)
    {k : Fin X.rCellCount} (hk : (cell X k).face ∉ faces) (A : CyclicArc (cellDarts X k))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) : False := by
  obtain ⟨X', P, C', i', A', s', ⟨e⟩, hlabel', hin, hout, hC', hCf', hi', hdec', hword⟩ :=
    enclosedLoopPocketRegionSucc_of_pieces.{u, w, v} enclosedBridgeDoublingSideArcSucc.{u, w, v}
      enclosedLoopPocketUnpinchSucc.{u, w, v} D (one_lt_length_of_two_le_rho hcondition hrho) X
      hlabel faces outerWalk E C hC hCf k hk A (s₁ ++ s₂) hdec
  have hdecomposition := split_decomposition i' s₁.length hdec'
  obtain ⟨cut⟩ := nonempty_osinMultipleEdgeCut_of_pocketRegion
    GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport hcondition hlambda1
    hc hlea (equiv.trans e) hlabel' P hin hout hC' hCf' hi' hi' (emptyArc (cellDarts X' i')) A'
    (s'.take s₁.length) (s'.drop s₁.length) hdecomposition
    (wordNorm_take_le hlabel hword hs₁) (wordNorm_drop_le hlabel hword hs₂)
  have hrho0 : 0 < rho := by omega
  exact cut.false_of_below o52LeastArea hcondition hlambda hmu hmu1 hrho0 hlarge hlea
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end Cut

/-- **Step 1 of the lake exclusion: filling the lakes of a full arc.**  A noncrossing cell pocket
walk between distinct cells, with the exterior off its side and a full arc, has an enclosed face
set turning to its successors, holding a relator cell, whose inverse outside walk reads two short
sides `s_1'`, `s_2'` and then either an arc of a cell outside, or nothing, when every relator cell
is inside. -/
def LakeFillSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j), i ≠ j →
    IsNoncrossingClosedWalk X.toCombMap K.walk →
    X.outerFace ∉ sideFaces X.toCombMap K.walk →
    (K.firstArc.length = (cellDarts X i).length ∨
      K.secondArc.length = (cellDarts X j).length) →
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
      (s₁ s₂ : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk ∧
        (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
        ((∃ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
            (cell X k).face ∉ faces ∧ invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts) ∨
          ((∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) ∧
            invDarts X outerWalk = s₁ ++ s₂))

/-- **Step 3 of the lake exclusion: a short loop cannot enclose every relator cell.**  At the
thresholds of `proof_of_gaps`, an O-equivalent copy of a least-area `Δ`, with clause (b) below `Δ`,
has no enclosed face set turning to its successors that holds a relator cell and every relator
cell, and whose inverse outside walk reads two sides of length at most `ε`. -/
def AllCellsShortLoopStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu →
    mu ≤ 1 / 16 → 2 ≤ rho → lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) →
    ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea →
      OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      OEquivalentDiscDiagram Delta X →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
        EnclosedFaceSetSucc X faces outerWalk →
        (∃ C ∈ X.relatorCells, C.face ∈ faces) →
        (∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) →
        ∀ s₁ s₂ : List X.toCombMap.Dart, invDarts X outerWalk = s₁ ++ s₂ →
          s₁.length ≤ eps → s₂.length ≤ eps → False

/-- **The lake exclusion from its two open steps.**  Steps 1 and 3 give the proper arcs of the cell
pocket walk below the inductive bound, at `ε₀ = 0` and `ρ₀ = max 2 ρ₁`; step 2 is
`false_of_enclosedSucc`. -/
theorem proof_of_gaps (hfill : LakeFillSuccStatement.{u, w, v})
    (hshort : AllCellsShortLoopStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho W hcondition => ?_⟩
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho
  intro Delta _ hlea hbelow S i j _ _ _ _ _ hij _ _ _ K _ _ _ _ hw hoff
  have hfalse : K.firstArc.length = (cellDarts S.diagram i).length ∨
      K.secondArc.length = (cellDarts S.diagram j).length → False := by
    intro hfull
    obtain ⟨faces, outerWalk, s₁, s₂, E, ⟨C, hC, hCf⟩, hs₁, hs₂, hcases⟩ :=
      hfill D eps S.diagram K hij hw hoff hfull
    rcases hcases with ⟨k, A, hk, hdec⟩ | ⟨hall, hdec⟩
    · exact false_of_enclosedSucc hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge hlea hbelow
        S.equiv S.label_admissible E hC hCf hk A hdec hs₁ hs₂
    · exact hshort D eps rho mu lambda c hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge Delta
        S.diagram hlea hbelow S.equiv S.label_admissible faces outerWalk E ⟨C, hC, hCf⟩ hall s₁ s₂
        hdec hs₁ hs₂
  exact ⟨lt_of_le_of_ne K.firstArc.length_le fun h => hfalse (Or.inl h),
    lt_of_le_of_ne K.secondArc.length_le fun h => hfalse (Or.inr h)⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.emptyArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.emptyArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.invDarts_emptyArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.dartWord_take_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.dartWord_drop_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.wordNorm_take_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.wordNorm_drop_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.split_decomposition
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.false_of_enclosedSucc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.proof_of_gaps
