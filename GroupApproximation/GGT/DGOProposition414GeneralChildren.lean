import GroupApproximation.GGT.DGOProposition414GeneralInput
import GroupApproximation.GGT.DGOProposition414GeneralArcQuasi
import GroupApproximation.GGT.DGOAssemblyChargeGeneral
import GroupApproximation.GGT.DGOProposition414GapIntervalProducer

/-!
# Genuine general-parameter estimates for every surgery child

The child words, cuts, distinguished components and their isolation are those
of the existing component surgery. Only the independently proved estimate on
non-distinguished sides is used to view them as general-parameter inputs.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

namespace AuxiliaryCycleCertificate

/-- A genuine estimate, independent of the certificate's bookkeeping error. -/
def QuasiAt {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (A : AuxiliaryCycleCertificate D b n) (mu err : ℝ) : Prop :=
  ∀ s : ℕ, s < n → s ∉ A.target → ∀ p q : ℕ,
    A.cut s ≤ p → p ≤ q → q ≤ A.cut (s + 1) →
    ((q - p : ℕ) : ℝ) / mu - err ≤
      ((wordDist D.alphabet.carrier
        (vertex A.basepoint A.word p) (vertex A.basepoint A.word q) : ℕ) : ℝ)

/-- Retain all the actual child data and use its genuine metric estimate. -/
def atParameters {D : RelGenSet G Λ} {b mu err : ℝ} {n : ℕ}
    (A : AuxiliaryCycleCertificate D b n) (h : A.QuasiAt mu err) :
    QuasiSumBoundInput D mu err n where
  basepoint := A.basepoint
  word := A.word
  cut := A.cut
  target := A.target
  label := A.label
  letters := A.letters
  closed := A.closed
  polygonCut := A.polygonCut
  target_lt := A.target_lt
  target_edge := A.target_edge
  target_component := A.target_component
  target_isolated := A.target_isolated
  quasi := h

end AuxiliaryCycleCertificate

/-- The four-path certificate has the supplied general estimate on its arc;
its remaining non-target sides lie on the geodesic chord. -/
theorem AuxiliaryCyclePathInput.certificate_quasi_at
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    (P : AuxiliaryCyclePathInput D hsymm b)
    (mu err : ℝ) (hmu : 1 ≤ mu) (herr : 0 ≤ err)
    (harc : ∀ r : ℕ, r < P.arcSides → P.left.length + r ∉ P.localTarget →
      ∀ p q : ℕ, P.arcCut r ≤ p → p ≤ q → q ≤ P.arcCut (r + 1) →
      ((q - p : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex (P.basepoint * RelLetter.listVal (revWord P.left)) P.arc p)
          (vertex (P.basepoint * RelLetter.listVal (revWord P.left)) P.arc q) : ℕ) : ℝ)) :
    P.certificate.QuasiAt mu err := by
  apply quasi_auxiliaryCycleWord_at D mu err hmu herr P.basepoint
    P.left P.arc P.right P.chord P.arcPolygon P.chordGeodesic
    (P.localTarget ∪ auxiliaryCycleConnectorTarget P.left P.right P.arcSides)
  · intro r hr hrTarget
    apply harc r hr
    exact fun h => hrTarget (Finset.mem_union.mpr (Or.inl h))
  · intro r hr
    exact Finset.mem_union.mpr <| Or.inr <|
      mem_auxiliaryCycleConnectorTarget_left P.left P.right P.arcSides r hr
  · intro r hr
    exact Finset.mem_union.mpr <| Or.inr <|
      mem_auxiliaryCycleConnectorTarget_right P.left P.right P.arcSides r hr

namespace BalancedSplitData

/-- Every first-half gap child preserves the genuine original parameters. -/
theorem firstGapChild_quasi_at
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (mu err : ℝ) (hmu : 1 ≤ mu) (herr : 0 ≤ err)
    (hquasi : ∀ s : ℕ, s < n → s ∉ P.target → ∀ p q : ℕ,
      P.cut s ≤ p → p ≤ q → q ≤ P.cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex P.basepoint P.word p) (vertex P.basepoint P.word q) : ℕ) : ℝ))
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (((B.gapIntervalsOfConfigurations C).toPathInput).first j).certificate.QuasiAt mu err := by
  apply AuxiliaryCyclePathInput.certificate_quasi_at _ mu err hmu herr
  intro r hr hrTarget p q hp hpq hq
  have hrestricted := IsCutPath.arcWord_quasi_at B.firstArc_isCutPath mu err
    B.firstArcTargetSides (B.firstArc_quasi_at mu err herr hquasi)
    (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
    (B.firstGapLocalTarget j) (B.firstGap_target_reflect j)
    r hr hrTarget p q hp hpq hq
  change ((q - p : ℕ) : ℝ) / mu - err ≤
    ((wordDist D.alphabet.carrier
      (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal (revWord (B.firstGapLeft j)))
        (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)) p)
      (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal (revWord (B.firstGapLeft j)))
        (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)) q) : ℕ) : ℝ)
  rw [B.firstGap_arcBase j]
  exact hrestricted

/-- Every wrapped-half gap child preserves the genuine original parameters. -/
theorem secondGapChild_quasi_at
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (mu err : ℝ) (hmu : 1 ≤ mu) (herr : 0 ≤ err)
    (hquasi : ∀ s : ℕ, s < n → s ∉ P.target → ∀ p q : ℕ,
      P.cut s ≤ p → p ≤ q → q ≤ P.cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex P.basepoint P.word p) (vertex P.basepoint P.word q) : ℕ) : ℝ))
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (((B.gapIntervalsOfConfigurations C).toPathInput).second j).certificate.QuasiAt mu err := by
  apply AuxiliaryCyclePathInput.certificate_quasi_at _ mu err hmu herr
  intro r hr hrTarget p q hp hpq hq
  have hrestricted := IsCutPath.arcWord_quasi_at B.secondArc_isCutPath mu err
    B.secondArcTargetSides (B.secondArc_quasi_at mu err herr hquasi)
    (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
    (B.secondGapLocalTarget j) (B.secondGap_target_reflect j)
    r hr hrTarget p q hp hpq hq
  change ((q - p : ℕ) : ℝ) / mu - err ≤
    ((wordDist D.alphabet.carrier
      (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j) *
        RelLetter.listVal (revWord (B.secondGapLeft j)))
        (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)) p)
      (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j) *
        RelLetter.listVal (revWord (B.secondGapLeft j)))
        (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)) q) : ℕ) : ℝ)
  rw [B.secondGap_arcBase j]
  exact hrestricted

end BalancedSplitData
end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.AuxiliaryCycleCertificate.atParameters
#audit_axioms GroupApproximation.GGT.DGOProposition414.AuxiliaryCyclePathInput.certificate_quasi_at
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChild_quasi_at
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChild_quasi_at
