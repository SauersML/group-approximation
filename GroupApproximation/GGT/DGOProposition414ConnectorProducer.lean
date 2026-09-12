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

/-- The canonical word for a single peripheral displacement.  The identity
displacement is represented by the empty path, so the construction never
introduces a spurious identity side. -/
noncomputable def compressedPeripheralWord (lam : Λ) (g : G) :
    List (RelLetter G Λ) := by
  classical
  exact if g = 1 then [] else [RelLetter.comp lam g]

namespace compressedPeripheralWord

theorem length_le_one (lam : Λ) (g : G) :
    (compressedPeripheralWord lam g).length ≤ 1 := by
  classical
  by_cases hg : g = 1 <;> simp [compressedPeripheralWord, hg]

theorem letters (D : RelGenSet G Λ) (lam : Λ) (g : G)
    (hg : g ∈ D.fam lam) :
    ∀ x ∈ compressedPeripheralWord lam g, D.IsLetter x := by
  classical
  intro x hx
  by_cases hone : g = 1
  · simp [compressedPeripheralWord, hone] at hx
  · have hx' : x = RelLetter.comp lam g := by
      simpa [compressedPeripheralWord, hone] using hx
    subst x
    exact hg

theorem label (lam : Λ) (g : G) :
    ∀ x ∈ compressedPeripheralWord lam g, x.IsCompOf lam := by
  classical
  intro x hx
  by_cases hone : g = 1
  · simp [compressedPeripheralWord, hone] at hx
  · have hx' : x = RelLetter.comp lam g := by
      simpa [compressedPeripheralWord, hone] using hx
    subst x
    simp [RelLetter.IsCompOf]

theorem listVal (lam : Λ) (g : G) :
    RelLetter.listVal (compressedPeripheralWord lam g) = g := by
  classical
  by_cases hg : g = 1
  · simp [compressedPeripheralWord, hg, RelLetter.listVal_nil]
  · simp [compressedPeripheralWord, hg, listVal_singleton, RelLetter.val]

end compressedPeripheralWord

/-- A word consisting entirely of admissible `lam`-letters has its value in
the peripheral subgroup `D.fam lam`. -/
theorem listVal_mem_fam_of_isCompOf (D : RelGenSet G Λ) (lam : Λ)
    (word : List (RelLetter G Λ))
    (letters : ∀ x ∈ word, D.IsLetter x)
    (label : ∀ x ∈ word, x.IsCompOf lam) :
    RelLetter.listVal word ∈ D.fam lam := by
  induction word with
  | nil => exact one_mem (D.fam lam)
  | cons x xs ih =>
      rw [listVal_cons]
      exact mul_mem
        (val_mem_fam_of_isCompOf D (letters x (by simp)) (label x (by simp)))
        (ih (fun y hy => letters y (by simp [hy]))
          (fun y hy => label y (by simp [hy])))

/-- The two connector words between a source component and its selected
partner component in one common half word. -/
structure ComponentConnectorPair (D : RelGenSet G Λ) (lam : Λ)
    (v : G) (word : List (RelLetter G Λ)) (source partner : ℕ) where
  sourceEnd : ℕ
  source_end_eq : sourceEnd = source + 1
  partnerEnd : ℕ
  source_span_mem :
    (vertex v word source)⁻¹ * vertex v word sourceEnd ∈ D.fam lam
  partner_end_eq : partnerEnd = partner + 1
  partner_span_mem :
    (vertex v word partner)⁻¹ * vertex v word partnerEnd ∈ D.fam lam
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
    (sourceSpan : (vertex v word source)⁻¹ *
      vertex v word (source + 1) ∈ D.fam lam)
    (partnerPos : partner < word.length)
    (partnerLetter : (word[partner]'partnerPos).IsCompOf lam)
    (connected : Connected D.fam lam v word source partner) :
    Nonempty (ComponentConnectorPair D lam v word source partner) := by
  have hpartnerSpan : (vertex v word partner)⁻¹ *
      vertex v word (partner + 1) ∈ D.fam lam := by
    rw [vertex_succ word v partner partnerPos]
    simpa only [inv_mul_cancel_left] using
      val_mem_fam_of_isCompOf D
        (letters _ (List.getElem_mem partnerPos)) partnerLetter
  obtain ⟨f, e, hf, he, hfLetters, heLetters, hfLabel, heLabel,
      hfValue, heValue⟩ :=
    exists_component_connector_pair D lam
      (pm := vertex v word source) (pp := vertex v word (source + 1))
      (ym := vertex v word partner) (yp := vertex v word (partner + 1))
      sourceSpan hpartnerSpan connected
  exact ⟨{
    sourceEnd := source + 1
    source_end_eq := rfl
    partnerEnd := partner + 1
    source_span_mem := sourceSpan
    partner_end_eq := rfl
    partner_span_mem := hpartnerSpan
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

/-- The source start joined directly to the far endpoint of the partner
component.  This is the source-faithful compression of `f * y` used when the
child chord must omit the partner edge adjacent to `f`. -/
noncomputable def startThroughPartner
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    List (RelLetter G Λ) :=
  compressedPeripheralWord lam
    ((vertex v word source)⁻¹ * vertex v word C.partnerEnd)

/-- The source end joined directly to the near endpoint of the partner
component.  This is the source-faithful compression of `e * y⁻¹` used when
the child chord must omit the partner edge adjacent to `e`. -/
noncomputable def endThroughPartner
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    List (RelLetter G Λ) :=
  compressedPeripheralWord lam
    ((vertex v word C.sourceEnd)⁻¹ * vertex v word partner)

theorem startThroughPartner_mem
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    (vertex v word source)⁻¹ * vertex v word C.partnerEnd ∈ D.fam lam := by
  have hfactor : (vertex v word source)⁻¹ * vertex v word C.partnerEnd =
      ((vertex v word source)⁻¹ * vertex v word partner) *
        ((vertex v word partner)⁻¹ * vertex v word C.partnerEnd) := by
    group
  rw [hfactor, ← C.start_value]
  exact mul_mem
    (listVal_mem_fam_of_isCompOf D lam C.startConnector
      C.start_letters C.start_label)
    C.partner_span_mem

theorem endThroughPartner_mem
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    (vertex v word C.sourceEnd)⁻¹ * vertex v word partner ∈ D.fam lam := by
  have hfactor : (vertex v word C.sourceEnd)⁻¹ * vertex v word partner =
      ((vertex v word C.sourceEnd)⁻¹ * vertex v word C.partnerEnd) *
        ((vertex v word partner)⁻¹ * vertex v word C.partnerEnd)⁻¹ := by
    group
  rw [hfactor]
  have hend := listVal_mem_fam_of_isCompOf D lam C.endConnector
    C.end_letters C.end_label
  rw [C.end_value] at hend
  exact mul_mem
    hend
    (inv_mem C.partner_span_mem)

theorem startThroughPartner_length
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    C.startThroughPartner.length ≤ 1 :=
  compressedPeripheralWord.length_le_one _ _

theorem endThroughPartner_length
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    C.endThroughPartner.length ≤ 1 :=
  compressedPeripheralWord.length_le_one _ _

theorem startThroughPartner_letters
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    ∀ x ∈ C.startThroughPartner, D.IsLetter x :=
  compressedPeripheralWord.letters D lam _ C.startThroughPartner_mem

theorem endThroughPartner_letters
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    ∀ x ∈ C.endThroughPartner, D.IsLetter x :=
  compressedPeripheralWord.letters D lam _ C.endThroughPartner_mem

theorem startThroughPartner_label
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    ∀ x ∈ C.startThroughPartner, x.IsCompOf lam :=
  compressedPeripheralWord.label lam _

theorem endThroughPartner_label
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    ∀ x ∈ C.endThroughPartner, x.IsCompOf lam :=
  compressedPeripheralWord.label lam _

theorem startThroughPartner_value
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    RelLetter.listVal C.startThroughPartner =
      (vertex v word source)⁻¹ * vertex v word C.partnerEnd :=
  compressedPeripheralWord.listVal _ _

theorem endThroughPartner_value
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    RelLetter.listVal C.endThroughPartner =
      (vertex v word C.sourceEnd)⁻¹ * vertex v word partner :=
  compressedPeripheralWord.listVal _ _

/-- The source component has the source-faithful three-factor quadrilateral
decomposition.  The connector factors are charged in source-half cut cycles;
the selected chord factor is charged in the opposite half. -/
theorem sourceSpan_three_factorization
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

/-- The exact distinguished edge in the first balanced half has its value in
the required peripheral subgroup.  This deliberately uses the one-edge
source span, rather than the possibly larger maximal component containing it:
the former is the endpoint which closes the inherited child arc. -/
theorem firstSourceSpan_mem
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.componentPlacement.firstTarget) :
    (vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.firstWord
          (B.componentPlacement.firstPos s + 1) ∈ D.fam (P.label s) := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hsTarget : s ∈ B.firstTarget := hs
  have hpos : B.componentPlacement.firstPos s = B.firstTargetPos s := rfl
  have hlt := B.firstTargetPos_lt hsTarget
  have hspan := span_mem_fam_of_isComp D P.basepoint P.letters
    (B.first_original_component hsTarget)
  rw [hpos]
  rw [BalancedSplitData.firstBase, ← hleft, BalancedSplitData.firstWord,
    vertex_firstHalf P.word P.basepoint B.refinedCut
      (show B.firstTargetPos s ≤
        B.refinedCut (B.secondSide + 2) -
          B.refinedCut (B.firstSide + 1) by
        simpa only [hleft, hright, firstArcLength] using hlt.le)
      hEnd B.chord,
    vertex_firstHalf P.word P.basepoint B.refinedCut
      (show B.firstTargetPos s + 1 ≤
        B.refinedCut (B.secondSide + 2) -
          B.refinedCut (B.firstSide + 1) by
        simp only [hleft, hright]
        simpa only [firstArcLength] using (Nat.succ_le_iff.mpr hlt))
      hEnd B.chord]
  simpa only [hleft, Nat.add_assoc] using hspan

/-- The exact distinguished edge in the wrapped balanced half has its value
in the required peripheral subgroup. -/
theorem secondSourceSpan_mem
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.componentPlacement.secondTarget) :
    (vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s))⁻¹ *
        vertex B.secondBase B.secondWord
          (B.componentPlacement.secondPos s + 1) ∈ D.fam (P.label s) := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hStartEnd : B.refinedCut (B.firstSide + 1) ≤
      B.refinedCut (B.secondSide + 2) := by
    rw [hleft, hright]
    exact B.split_vertices_ordered
  have hsTarget : s ∈ B.secondTarget := hs
  have hpos : B.componentPlacement.secondPos s = B.secondTargetPos s := rfl
  have hlt := B.secondTargetPos_lt hsTarget
  have hspan := span_mem_fam_of_isComp D B.secondBase
    (letters_rotWord D P.letters B.secondVertex)
    (B.second_rotated_component hsTarget)
  rw [hpos]
  rw [BalancedSplitData.secondBase, ← hright, BalancedSplitData.secondWord,
    vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut hStartEnd hEnd
      (show B.secondTargetPos s ≤
        (P.word.length - B.refinedCut (B.secondSide + 2)) +
          B.refinedCut (B.firstSide + 1) by
        simpa only [hleft, hright, secondArcLength] using hlt.le)
      B.chord,
    vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut hStartEnd hEnd
      (show B.secondTargetPos s + 1 ≤
        (P.word.length - B.refinedCut (B.secondSide + 2)) +
          B.refinedCut (B.firstSide + 1) by
        simp only [hleft, hright]
        simpa only [secondArcLength] using (Nat.succ_le_iff.mpr hlt))
      B.chord]
  simpa only [hright, BalancedSplitData.secondBase] using hspan

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
    (B.firstSourceSpan_mem s hsTarget)
    (B.brokenAssignment.first.partner_pos_lt s hs)
    (B.brokenAssignment.first.partner_letter s hs)
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
    (B.secondSourceSpan_mem s hsTarget)
    (B.brokenAssignment.second.partner_pos_lt s hs)
    (B.brokenAssignment.second.partner_letter s hs)
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
