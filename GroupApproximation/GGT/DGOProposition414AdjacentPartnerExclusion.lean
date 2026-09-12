import GroupApproximation.GGT.DGOProposition414GapChordHead
import GroupApproximation.GGT.DGOProposition414GapRightConnectorWrapped

/-!
# Adjacent partner edges are removed from each child chord

The child chord runs between the appropriate near endpoints of the adjacent
partner edges. Neither edge belongs to that oriented segment. These exact
exclusions are the positional input for connector-target separation, including
initial and terminal gaps and either ordering of the two partners.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The previous broken source's partner is outside its first-gap chord. -/
theorem firstGapChord_not_edge_previous
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p) :
    ¬ EdgeBetween (B.firstGapChordStart j) (B.firstGapChordFinish j)
      (B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first p)) := by
  classical
  cases hn : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none =>
    have hlt := B.brokenAssignment.first.partner_lt _
      (HalfEntry.entrySource_mem B.brokenAssignment.index.first p)
    simp only [firstGapChordStart, firstGapChordFinish, firstGapRunsForward, hp, hn, EdgeBetween, ↓reduceIte]
    omega
  | some e =>
    have hne : B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first p) ≠
        B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
      intro heq
      exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.first j hp hn
        (B.brokenAssignment.first.partner_injective
          (HalfEntry.entrySource_mem B.brokenAssignment.index.first p)
          (HalfEntry.entrySource_mem B.brokenAssignment.index.first e) heq)
    simp only [firstGapChordStart, firstGapChordFinish, firstGapRunsForward, hp, hn, EdgeBetween]
    split_ifs <;> omega

/-- The next broken source's partner is outside its first-gap chord. -/
theorem firstGapChord_not_edge_next
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.first j = some e) :
    ¬ EdgeBetween (B.firstGapChordStart j) (B.firstGapChordFinish j)
      (B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
  classical
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none =>
    simp only [firstGapChordStart, firstGapChordFinish, firstGapRunsForward, hp, hn, EdgeBetween, ↓reduceIte]
    omega
  | some p =>
    have hne : B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first p) ≠
        B.brokenAssignment.first.partner (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
      intro heq
      exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.first j hp hn
        (B.brokenAssignment.first.partner_injective
          (HalfEntry.entrySource_mem B.brokenAssignment.index.first p)
          (HalfEntry.entrySource_mem B.brokenAssignment.index.first e) heq)
    simp only [firstGapChordStart, firstGapChordFinish, firstGapRunsForward, hp, hn, EdgeBetween]
    split_ifs <;> omega

/-- The previous broken source's partner is outside its second-gap chord. -/
theorem secondGapChord_not_edge_previous
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p) :
    ¬ EdgeBetween (B.secondGapChordStart j) (B.secondGapChordFinish j)
      (B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second p)) := by
  classical
  cases hn : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none =>
    simp only [secondGapChordStart, secondGapChordFinish, secondGapRunsForward, hp, hn, EdgeBetween, ↓reduceIte]
    omega
  | some e =>
    have hne : B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second p) ≠
        B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
      intro heq
      exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.second j hp hn
        (B.brokenAssignment.second.partner_injective
          (HalfEntry.entrySource_mem B.brokenAssignment.index.second p)
          (HalfEntry.entrySource_mem B.brokenAssignment.index.second e) heq)
    simp only [secondGapChordStart, secondGapChordFinish, secondGapRunsForward, hp, hn, EdgeBetween]
    split_ifs <;> omega

/-- The next broken source's partner is outside its second-gap chord. -/
theorem secondGapChord_not_edge_next
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.second j = some e) :
    ¬ EdgeBetween (B.secondGapChordStart j) (B.secondGapChordFinish j)
      (B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
  classical
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none =>
    have hlt := B.brokenAssignment.second.partner_lt _
      (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)
    simp only [secondGapChordStart, secondGapChordFinish, secondGapRunsForward, hp, hn, EdgeBetween, ↓reduceIte]
    omega
  | some p =>
    have hne : B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second p) ≠
        B.brokenAssignment.second.partner (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
      intro heq
      exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.second j hp hn
        (B.brokenAssignment.second.partner_injective
          (HalfEntry.entrySource_mem B.brokenAssignment.index.second p)
          (HalfEntry.entrySource_mem B.brokenAssignment.index.second e) heq)
    simp only [secondGapChordStart, secondGapChordFinish, secondGapRunsForward, hp, hn, EdgeBetween]
    split_ifs <;> omega

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChord_not_edge_previous

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChord_not_edge_next

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChord_not_edge_previous

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChord_not_edge_next
