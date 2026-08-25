import GroupApproximation.Manuscript.OneSidedMFRadical.FaithfulCornerCoronaRepresentation
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerGramSequence
import GroupApproximation.Manuscript.OneSidedMFRadical.FaithfulCornerNormBridge

/-!
# Assembly of the printed corrected-corner trace passage

This file removes the two construction premises that remained in the
faithful-representation version of the printed argument:

* the faithful Hilbert-space representation is the universal direct-sum GNS
  representation from `FaithfulCornerCoronaRepresentation`;
* the bounded representative of the positive Gram element is the literal
  sequence of Gram matrices of `PrintedCornerData.cornerMap` from
  `CorrectedCornerGramSequence`.

Thus the theorem below assumes only the Kazhdan quadratic-form inequality for
that fixed operator and concludes the manuscript's eventual normalized-corner
trace inequality.  No representation-existence or bounded-sequence-existence
hypothesis remains.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]
variable {model : ℕ → FiniteModel}

/-- The fixed Hilbert space on which the corrected-corner omega corona is
represented faithfully. -/
abbrev CorrectedCornerFaithfulSpace (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) :=
  CornerCoronaFaithfulSpace (fun n ↦ D.cornerModel n) ω

/-- The actual bounded Gram sequence, viewed as an element of the omega
matrix corona. -/
noncomputable def correctedCornerGramClass (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) (S : Finset G) :
    FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) (ω : Filter ℕ) :=
  filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
    (correctedCornerSectorGramSequence D S)

/-- The fixed represented positive Gram element to which the Kazhdan lower
quadratic-form bound applies. -/
noncomputable def correctedCornerGramOperator (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) (S : Finset G) :
    CorrectedCornerFaithfulSpace D ω →L[ℂ]
      CorrectedCornerFaithfulSpace D ω :=
  cornerCoronaFaithfulRepresentation (fun n ↦ D.cornerModel n) ω
    (correctedCornerGramClass D ω S)

/-- **Unconditional assembly of the manuscript's corner-trace passage.**

The hypothesis is exactly the load-bearing Kazhdan assertion for the one
operator fixed above.  The conclusion is the printed inequality

`(c-o(1))/|S| ≤ |S|⁻¹ ∑_{s∈S} ‖W_n(s)-1‖₂²`

along the chosen ultrafilter, with `W_n(s)` definitionally the actual
polar-corrected corner map.  Both former assembly inputs -- an arbitrary
faithful representation and an arbitrary bounded representative `bseq` --
have disappeared from the statement. -/
theorem eventually_correctedCorner_trace_inequality
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ) (S : Finset G)
    (c : ℝ)
    (hquad : ∀ x : CorrectedCornerFaithfulSpace D ω,
      c * ‖x‖ ^ 2 ≤ (⟪x, correctedCornerGramOperator D ω S x⟫_ℂ).re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in (ω : Filter ℕ), (c - epsilon) / S.card ≤
      (S.card : ℝ)⁻¹ * ∑ s ∈ S,
        hsNormSq (D.cornerModel n)
          ((D.cornerMap n s :
            Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1) := by
  apply eventually_printed_corner_trace_inequality_of_faithful
    (fun n ↦ D.cornerModel n) (ω : Filter ℕ) S
    (fun n s ↦ (D.cornerMap n s :
      Matrix (D.cornerModel n) (D.cornerModel n) ℂ))
    (correctedCornerSectorGramSequence D S)
    (correctedCornerSectorGramSequence_apply D S)
    (cornerCoronaFaithfulRepresentation (fun n ↦ D.cornerModel n) ω)
    (cornerCoronaFaithfulRepresentation_injective
      (fun n ↦ D.cornerModel n) ω)
    c
  · simpa only [correctedCornerGramOperator, correctedCornerGramClass] using hquad
  · exact hepsilon

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
