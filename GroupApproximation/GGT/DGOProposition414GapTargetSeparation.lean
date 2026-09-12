import GroupApproximation.GGT.DGOProposition414FirstArcIsolation
import GroupApproximation.GGT.DGOProposition414SecondArcIsolation
import GroupApproximation.GGT.DGOProposition414FirstChargedIsolation
import GroupApproximation.GGT.DGOProposition414SecondChargedIsolation
import GroupApproximation.GGT.DGOProposition414FirstConnectorIsolation
import GroupApproximation.GGT.DGOProposition414SecondConnectorIsolation
import GroupApproximation.GGT.DGOProposition414SecondSeparationTargets

/-!
# Full target separation for every balanced-split auxiliary cycle

Inherited targets, charged partner targets, and both connector target classes
are isolated against every component start. This discharges the two original
target-separation predicates consumed by the component-family assembly.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- All four target classes are separated from every distinct component start. -/
theorem firstGapTargetSeparation
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R) :
    FirstGapTargetSeparation B := by
  intro j s hs
  rcases B.firstGapTarget_cases j hs with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | hleft | ⟨r, hr, rfl⟩
  · exact (B.firstGapArcSource_cycleIsolated j t ht).2
  · exact (B.firstGapChordSource_cycleIsolated j t ht).2
  · have hlen := B.firstGapLeft_length_le_one j
    have hs0 : s = 0 := by omega
    subst s
    cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
    | none =>
      have hnil : B.firstGapLeft j = [] := by simp only [firstGapLeft]; rw [hp]
      simp [hnil] at hleft
    | some p =>
      rw [B.firstGapLocalLabel_leftConnector j p hp 0 hleft,
        B.firstGapCut_left j (Nat.zero_le _)]
      exact (B.firstGapLeft_cycleIsolated j p hp hleft).2
  · have hlen := B.firstGapRight_length_le_one j
    have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.add_zero]
    cases hn : HalfGap.nextEntry B.brokenAssignment.index.first j with
    | none =>
      have hnil : B.firstGapRight j = [] := by simp only [firstGapRight]; rw [hn]
      simp [hnil] at hr
    | some e =>
      have hlabel := B.firstGapLocalLabel_rightConnector j e hn 0 hr
      have hcut := B.firstGapCut_right j (r := 0) (Nat.zero_le _)
      simp only [Nat.add_zero] at hlabel hcut
      rw [hlabel, hcut]
      exact (B.firstGapRight_cycleIsolated j e hn hr).2

/-- All four target classes are separated from every distinct component start. -/
theorem secondGapTargetSeparation
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R) :
    SecondGapTargetSeparation B := by
  intro j s hs
  rcases B.secondGapTarget_cases j hs with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | hleft | ⟨r, hr, rfl⟩
  · exact (B.secondGapArcSource_cycleIsolated j t ht).2
  · exact (B.secondGapChordSource_cycleIsolated j t ht).2
  · have hlen := B.secondGapLeft_length_le_one j
    have hs0 : s = 0 := by omega
    subst s
    cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
    | none =>
      have hnil : B.secondGapLeft j = [] := by simp only [secondGapLeft]; rw [hp]
      simp [hnil] at hleft
    | some p =>
      rw [B.secondGapLocalLabel_leftConnector j p hp 0 hleft,
        B.secondGapCut_left j (Nat.zero_le _)]
      exact (B.secondGapLeft_cycleIsolated j p hp hleft).2
  · have hlen := B.secondGapRight_length_le_one j
    have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.add_zero]
    cases hn : HalfGap.nextEntry B.brokenAssignment.index.second j with
    | none =>
      have hnil : B.secondGapRight j = [] := by simp only [secondGapRight]; rw [hn]
      simp [hnil] at hr
    | some e =>
      have hlabel := B.secondGapLocalLabel_rightConnector j e hn 0 hr
      have hcut := B.secondGapCut_right j (r := 0) (Nat.zero_le _)
      simp only [Nat.add_zero] at hlabel hcut
      rw [hlabel, hcut]
      exact (B.secondGapRight_cycleIsolated j e hn hr).2

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapTargetSeparation

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapTargetSeparation
