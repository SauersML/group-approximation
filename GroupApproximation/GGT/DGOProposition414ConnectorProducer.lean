import GroupApproximation.GGT.DGOProposition414TargetTransport
import GroupApproximation.GGT.DGOAssemblyCharge

/-!
# Canonical connector words for the broken balanced components

The retained broken-component incidences determine both connector words.
This file performs that choice simultaneously over the two balanced halves,
retaining the component endpoints and all word/value facts needed by the
interval surgery.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The two connector words between a source component and its selected
partner component in one common half word. -/
structure ComponentConnectorPair (D : RelGenSet G Λ) (lam : Λ)
    (v : G) (word : List (RelLetter G Λ)) (source partner : ℕ) where
  sourceEnd : ℕ
  partnerEnd : ℕ
  sourceComponent : IsComp lam word source sourceEnd
  partnerComponent : IsComp lam word partner partnerEnd
  startConnector : List (RelLetter G Λ)
  endConnector : List (RelLetter G Λ)
  start_length : startConnector.length ≤ 1
  end_length : endConnector.length ≤ 1
  start_letters : ∀ x ∈ startConnector, D.IsLetter x
  end_letters : ∀ x ∈ endConnector, D.IsLetter x
  start_label : ∀ x ∈ startConnector, x.IsCompOf lam
  end_label : ∀ x ∈ endConnector, x.IsCompOf lam
  start_value : RelLetter.listVal startConnector =
    (vertex v word source)⁻¹ * vertex v word partner
  end_value : RelLetter.listVal endConnector =
    (vertex v word sourceEnd)⁻¹ * vertex v word partnerEnd

/-- Component starts and their retained connected incidence construct the two
connector words without any further geometric premise. -/
theorem exists_componentConnectorPair
    (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (word : List (RelLetter G Λ))
    (letters : ∀ x ∈ word, D.IsLetter x) (source partner : ℕ)
    (sourceStart : IsCompStart lam word source)
    (partnerStart : IsCompStart lam word partner)
    (connected : Connected D.fam lam v word source partner) :
    Nonempty (ComponentConnectorPair D lam v word source partner) := by
  obtain ⟨sourceEnd, hsource⟩ := sourceStart
  obtain ⟨partnerEnd, hpartner⟩ := partnerStart
  have hsourceSpan := span_mem_fam_of_isComp D v letters hsource
  have hpartnerSpan := span_mem_fam_of_isComp D v letters hpartner
  obtain ⟨f, e, hf, he, hfLetters, heLetters, hfLabel, heLabel,
      hfValue, heValue⟩ :=
    exists_component_connector_pair D lam hsourceSpan hpartnerSpan connected
  exact ⟨{
    sourceEnd := sourceEnd
    partnerEnd := partnerEnd
    sourceComponent := hsource
    partnerComponent := hpartner
    startConnector := f
    endConnector := e
    start_length := hf
    end_length := he
    start_letters := hfLetters
    end_letters := heLetters
    start_label := hfLabel
    end_label := heLabel
    start_value := hfValue
    end_value := heValue
  }⟩

namespace ComponentConnectorPair

/-- The source component is the connector--partner--connector boundary
product, with the terminal connector read in reverse. -/
theorem sourceSpan_factorization
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    (vertex v word source)⁻¹ * vertex v word C.sourceEnd =
      RelLetter.listVal C.startConnector *
        ((vertex v word partner)⁻¹ * vertex v word C.partnerEnd) *
        (RelLetter.listVal C.endConnector)⁻¹ := by
  rw [C.start_value, C.end_value]
  group

/-- Both connectors contribute at most two child sides. -/
theorem connector_length_sum_le
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    C.startConnector.length + C.endConnector.length ≤ 2 := by
  have hs := C.start_length
  have he := C.end_length
  omega

end ComponentConnectorPair

namespace BalancedSplitData

/-- Every letter of the concrete first balanced half is admissible. -/
theorem firstWord_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ x ∈ B.firstWord, D.IsLetter x := by
  unfold firstWord
  exact isLetter_firstHalf D hsymm P.letters B.chord_geodesic.1
    B.refinedCut (B.firstSide + 1) (B.secondSide + 2)

/-- Every letter of the concrete wrapped second balanced half is admissible. -/
theorem secondWord_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ x ∈ B.secondWord, D.IsLetter x := by
  unfold secondWord
  exact isLetter_secondHalf D P.letters B.chord_geodesic.1
    B.refinedCut (B.firstSide + 1) (B.secondSide + 2)

/-- Canonical connector data for one broken source in the first half. -/
noncomputable def firstBrokenConnectors
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    ComponentConnectorPair D (P.label s) B.firstBase B.firstWord
      (B.componentPlacement.firstPos s)
      (B.firstChordPos (B.brokenAssignment.first.partner s)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  exact Classical.choice (exists_componentConnectorPair D (P.label s)
    B.firstBase B.firstWord B.firstWord_letters
    (B.componentPlacement.firstPos s)
    (B.firstChordPos (B.brokenAssignment.first.partner s))
    (B.componentPlacement.first_start s hsTarget)
    (B.brokenAssignment.first.partner_start s hs)
    (B.brokenAssignment.first.partner_connected s hs))

/-- Canonical connector data for one broken source in the wrapped half. -/
noncomputable def secondBrokenConnectors
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    ComponentConnectorPair D (P.label s) B.secondBase B.secondWord
      (B.componentPlacement.secondPos s)
      (B.secondChordPos (B.brokenAssignment.second.partner s)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  exact Classical.choice (exists_componentConnectorPair D (P.label s)
    B.secondBase B.secondWord B.secondWord_letters
    (B.componentPlacement.secondPos s)
    (B.secondChordPos (B.brokenAssignment.second.partner s))
    (B.componentPlacement.second_start s hsTarget)
    (B.brokenAssignment.second.partner_start s hs)
    (B.brokenAssignment.second.partner_connected s hs))

/-- Both broken-half connector families, indexed by the exact broken sets used
by the greedy interval decomposition. -/
structure BrokenConnectorFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  first : ∀ s, s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives →
    ComponentConnectorPair D (P.label s) B.firstBase B.firstWord
      (B.componentPlacement.firstPos s)
      (B.firstChordPos (B.brokenAssignment.first.partner s))
  second : ∀ s, s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives →
    ComponentConnectorPair D (P.label s) B.secondBase B.secondWord
      (B.componentPlacement.secondPos s)
      (B.secondChordPos (B.brokenAssignment.second.partner s))

/-- The retained incidences produce the complete two-half connector family
canonically. -/
noncomputable def brokenConnectorFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    BrokenConnectorFamily B where
  first := B.firstBrokenConnectors
  second := B.secondBrokenConnectors

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
