import GroupApproximation.Analysis.RankNormalizedHilbertization
import GroupApproximation.Sofic.TransportVariantsAnyUniverse

/-!
# The transport theorem at the collapse proof's rank weight

Proof-ledger row `CO.14c`.  The sentence is the one that follows
that weighted transport theorem in `non_mf_groups_exist.tex` (navigate by the label;
the file is under concurrent edit):

> Taking `ν_n = d_n` gives Theorem `thm:kazhdan-transport` with the uniform
> operator-norm bound relaxed to a uniform bound on `Tr(x_n* x_n)/d_n`.
> Taking `ν_n = k_n`, the rank of the projection lift in the proof of
> Theorem `thm:projection-collapse`, gives the normalization used there.

The first half is already in the corpus, as
`ScaledKazhdanTransport.manuscriptDimensionWeightRecovery`.  The second half
was the finding of row `CO.14c`: the rank weight is genuinely carried through
the collapse proof, but the collapse re-derives its bound inline, so the
printed deduction *from a previously proved theorem* had no Lean counterpart —
neither `scaled_transport_both` nor its any-universe form was ever invoked at
the weight `ν_n = k_n`.

This file supplies that invocation.  `rankTransportWeight B Q` is literally
`n ↦ rank (Q n)`, the rank of the projection lift `Q_n` of the collapse
proof's Step 3, and:

* `rank_weight_transport_both` is that weighted transport theorem, clause 1, at that weight,
  obtained by instantiating `scaled_transport_both_anyUniverse` — no new
  argument, and in particular no inline re-derivation;
* `isScaledMassBounded_rankWeight_of_rank_le` is the hypothesis feed: the
  printed mass bound `Tr(x_n* x_n) ≤ C ν_n` at `ν_n = k_n` holds for exactly
  the families the collapse produces, namely the coordinate representatives
  of the ideal `Q q Q`, by `eq:rank-frobenius`;
* `rank_weight_transport_both_of_idealSum` chains the two, so that a
  coordinate representative `Z_n = ∑_{j < r} X_{j,n} Q_n Y_{j,n}` with
  uniformly bounded operator norm is transported by the compressor with no
  further hypothesis.

The `∀ n, 0 ≤ ν_n` side condition of the transport theorem is discharged by
`Nat.cast_nonneg`: a rank is a natural number.
-/

namespace GroupApproximation
namespace CollapseRankWeightTransport

open Matrix ScaledKazhdanTransport
open RankNormalizedHilbertization
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {Γ : Type v} {E : Type u} [Group Γ] [Group E]

/-- **The collapse proof's weight.**  `ν_n = k_n = rank Q_n`, where `Q_n` is
the projection lift of `q` fixed in Step 3 of the proof of
`thm:projection-collapse`. -/
def rankTransportWeight (B : OpAlmostRepresentation E)
    (Q : ∀ n, Matrix (B.model n) (B.model n) ℂ) : ℕ → ℝ :=
  fun n ↦ ((Q n).rank : ℝ)

theorem rankTransportWeight_nonneg (B : OpAlmostRepresentation E)
    (Q : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    ∀ n, 0 ≤ rankTransportWeight B Q n := fun _ ↦ Nat.cast_nonneg _

/-- **that weighted transport theorem, clause 1, at `ν_n = k_n`.**  The two-sided scaled
transport theorem, read at the rank of the projection lift.  This is the
printed *"taking `ν_n = k_n` … gives the normalization used there"*: the
statement is an instance of the already-proved theorem, not a re-derivation. -/
theorem rank_weight_transport_both (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E)
    (Q x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C x)
    (hbound : IsScaledMassBounded B (rankTransportWeight B Q) x) :
    IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  TransportVariantsAnyUniverse.scaled_transport_both_anyUniverse B
    (rankTransportWeight B Q) (rankTransportWeight_nonneg B Q) C x hx hbound

/-- **The printed mass bound at the rank weight.**  `Tr(x_n* x_n) ≤ C k_n`
holds for any coordinate family of uniformly bounded operator norm whose rank
is `O(k_n)`, by `eq:rank-frobenius`.  This is what makes the hypothesis of
that weighted transport theorem, clause 1, available at `ν_n = k_n`. -/
theorem isScaledMassBounded_rankWeight_of_rank_le (B : OpAlmostRepresentation E)
    (Q x : ∀ n, Matrix (B.model n) (B.model n) ℂ) (r : ℕ) (Cop : ℝ)
    (hrank : ∀ n, (x n).rank ≤ r * (Q n).rank)
    (hnorm : ∀ n, ‖x n‖ ≤ Cop) :
    IsScaledMassBounded B (rankTransportWeight B Q) x := by
  refine ⟨(r : ℝ) * Cop ^ 2, by positivity, fun n ↦ ?_⟩
  show matMass (x n) ≤ (r : ℝ) * Cop ^ 2 * ((Q n).rank : ℝ)
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hrk : (0 : ℝ) ≤ ((Q n).rank : ℝ) := Nat.cast_nonneg _
  have h2 : ((x n).rank : ℝ) ≤ (r : ℝ) * ((Q n).rank : ℝ) := by
    exact_mod_cast hrank n
  have h3 : ‖x n‖ ^ 2 ≤ Cop ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖x n‖ := norm_nonneg _
    nlinarith [hnorm n]
  calc matMass (x n) ≤ ((x n).rank : ℝ) * ‖x n‖ ^ 2 :=
        InvolutionRankMass.matMass_le_rank_mul_sq_opNorm (x n)
    _ ≤ ((r : ℝ) * ((Q n).rank : ℝ)) * ‖x n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ ≤ ((r : ℝ) * ((Q n).rank : ℝ)) * Cop ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hr hrk)
    _ = (r : ℝ) * Cop ^ 2 * ((Q n).rank : ℝ) := by ring

/-- **CO.14c, chained.**  A coordinate representative
`Z_n = ∑_{j < r} X_{j,n} Q_n Y_{j,n}` of an element of the ideal `Q q Q`,
with uniformly bounded operator norm and asymptotically commuting with the
Kazhdan image at the rank weight, is transported by the compressor on both
sides.  The rank bound is `rank_idealSum_le`, the mass bound is
`eq:rank-frobenius`, and the transport is that weighted transport theorem, clause 1,. -/
theorem rank_weight_transport_both_of_idealSum (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E)
    (Q : ∀ n, Matrix (B.model n) (B.model n) ℂ) (r : ℕ) (Cop : ℝ)
    (X Z : ℕ → ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hnorm : ∀ n, ‖∑ j ∈ Finset.range r, X j n * Q n * Z j n‖ ≤ Cop)
    (hx : IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C
      (fun n ↦ ∑ j ∈ Finset.range r, X j n * Q n * Z j n)) :
    IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) *
            (∑ j ∈ Finset.range r, X j n * Q n * Z j n) *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsScaledAsymptoticCommutant B (rankTransportWeight B Q) C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            (∑ j ∈ Finset.range r, X j n * Q n * Z j n) *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  rank_weight_transport_both B C Q _ hx
    (isScaledMassBounded_rankWeight_of_rank_le B Q _ r Cop
      (fun n ↦ rank_idealSum_le r (Q n) (fun j ↦ X j n) (fun j ↦ Z j n))
      hnorm)

end

end CollapseRankWeightTransport
end GroupApproximation
