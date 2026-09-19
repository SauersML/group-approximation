import GroupApproximation.Algebra.WordMetric
import GroupApproximation.Sofic.InvolutionRankMass
import GroupApproximation.Sofic.ProjectionRankFlip

/-!
# Rank self-normalization for an exactly covariant finite packet

This file is the noncommutative replacement for the commuting-involution
word bound.  It assumes only exact unitary covariance of a matrix-valued
orbit along a finite generating set.  Pairwise commutation of orbit values is
never used.

The integer weight is the sum of the generator displacement ranks.  Exact
covariance and rank subadditivity imply that the displacement of a word has
rank at most its length times that weight.  Consequently its Frobenius mass
has the same bound up to the universal factor `4`.
-/

namespace GroupApproximation
namespace FinitePacketRankWeight

open Matrix InvolutionRankMass KazhdanCornerMatrices
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Γ Y : Type*} [Group Γ] [Fintype Y] [DecidableEq Y]

/-- Rank displacement from the distinguished packet value `V 1`. -/
def displacementRank (V : Γ → Matrix Y Y ℂ) (g : Γ) : ℕ :=
  (V g - V 1).rank

/-- The self-generated integer scale: total generator displacement rank. -/
def generatorRankWeight (V : Γ → Matrix Y Y ℂ) (S : Finset Γ) : ℕ :=
  ∑ a ∈ S, displacementRank V a

omit [DecidableEq Y] in
/-- Each generator displacement is bounded by the total rank weight. -/
theorem displacementRank_le_generatorRankWeight
    (V : Γ → Matrix Y Y ℂ) (S : Finset Γ) {a : Γ} (ha : a ∈ S) :
    displacementRank V a ≤ generatorRankWeight V S := by
  unfold generatorRankWeight
  exact Finset.single_le_sum (f := fun g ↦ displacementRank V g)
    (fun _ _ ↦ Nat.zero_le _) ha

/-- One exactly covariant left-translation step costs at most one generator
displacement rank. -/
theorem displacementRank_mul_le
    (V : Γ → Matrix Y Y ℂ) (U : Γ → Matrix Y Y ℂ)
    {a g : Γ} (hU : U a ∈ Matrix.unitaryGroup Y ℂ)
    (hcov : ∀ x : Γ, V (a * x) = U a * V x * (U a)ᴴ) :
    displacementRank V (a * g) ≤
      displacementRank V g + displacementRank V a := by
  have hbase : V a = U a * V 1 * (U a)ᴴ := by
    simpa using hcov 1
  have hsplit : V (a * g) - V 1 =
      U a * (V g - V 1) * (U a)ᴴ + (V a - V 1) := by
    rw [hcov g, hbase]
    noncomm_ring
  unfold displacementRank
  rw [hsplit]
  calc
    (U a * (V g - V 1) * (U a)ᴴ + (V a - V 1)).rank ≤
        (U a * (V g - V 1) * (U a)ᴴ).rank + (V a - V 1).rank :=
      rank_add_le _ _
    _ = (V g - V 1).rank + (V a - V 1).rank := by
      rw [rank_unitary_conj hU]

/-- Induction along an arbitrary word in the generating set. -/
theorem displacementRank_prod_le
    (V : Γ → Matrix Y Y ℂ) (U : Γ → Matrix Y Y ℂ) (S : Finset Γ)
    (hU : ∀ a ∈ S, U a ∈ Matrix.unitaryGroup Y ℂ)
    (hcov : ∀ a ∈ S, ∀ g : Γ, V (a * g) = U a * V g * (U a)ᴴ)
    (l : List Γ) (hl : ∀ a ∈ l, a ∈ S) :
    displacementRank V l.prod ≤ l.length * generatorRankWeight V S := by
  induction l with
  | nil =>
      simp [displacementRank]
  | cons a l ih =>
      have ha : a ∈ S := hl a List.mem_cons_self
      have htail : ∀ x ∈ l, x ∈ S :=
        fun x hx ↦ hl x (List.mem_cons_of_mem a hx)
      calc
        displacementRank V (a :: l).prod =
            displacementRank V (a * l.prod) := by rw [List.prod_cons]
        _ ≤ displacementRank V l.prod + displacementRank V a :=
          displacementRank_mul_le V U (hU a ha) (hcov a ha)
        _ ≤ l.length * generatorRankWeight V S + generatorRankWeight V S :=
          Nat.add_le_add (ih htail)
            (displacementRank_le_generatorRankWeight V S ha)
        _ = (a :: l).length * generatorRankWeight V S := by
          simp only [List.length_cons, Nat.add_mul, one_mul]

/-- The exact rank word bound at the genuine shortest-word norm. -/
theorem displacementRank_le_wordNorm_mul
    (V : Γ → Matrix Y Y ℂ) (U : Γ → Matrix Y Y ℂ) (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hU : ∀ a ∈ S, U a ∈ Matrix.unitaryGroup Y ℂ)
    (hcov : ∀ a ∈ S, ∀ g : Γ, V (a * g) = U a * V g * (U a)ᴴ)
    (g : Γ) :
    displacementRank V g ≤
      WordMetric.wordNorm (S : Set Γ) g * generatorRankWeight V S := by
  obtain ⟨l, hl, hlen⟩ := WordMetric.exists_isWord_length_eq hgen g
  have h := displacementRank_prod_le V U S hU hcov l
    (fun a ha ↦ Finset.mem_coe.mp (hl.letters a ha))
  rwa [hl.prod_eq, hlen] at h

/-- A difference of two unitary matrices has operator norm at most `2`. -/
theorem norm_sub_le_two_of_unitary (hY : Nonempty Y)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    ‖A - B‖ ≤ 2 := by
  haveI := hY
  have hAnorm : ‖A‖ = 1 := CStarRing.norm_of_mem_unitary hA
  have hBnorm : ‖B‖ = 1 := CStarRing.norm_of_mem_unitary hB
  calc
    ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    _ = 2 := by rw [hAnorm, hBnorm]; norm_num

/-- Frobenius mass is controlled by rank for a difference of packet
unitaries. -/
theorem displacementMass_le_four_mul_rank (hY : Nonempty Y)
    (V : Γ → Matrix Y Y ℂ)
    (hV : ∀ g : Γ, V g ∈ Matrix.unitaryGroup Y ℂ) (g : Γ) :
    matMass (V g - V 1) ≤ 4 * displacementRank V g := by
  have hn : ‖V g - V 1‖ ≤ 2 :=
    norm_sub_le_two_of_unitary hY (hV g) (hV 1)
  have hsq : ‖V g - V 1‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (V g - V 1)]
  calc
    matMass (V g - V 1) ≤
        ((V g - V 1).rank : ℝ) * ‖V g - V 1‖ ^ 2 :=
      matMass_le_rank_mul_sq_opNorm _
    _ ≤ ((V g - V 1).rank : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = 4 * displacementRank V g := by
      rw [mul_comm]
      rfl

/-- The paper's rank-weight mass estimate, with no commutativity hypothesis. -/
theorem displacementMass_le_four_mul_wordNorm_mul_weight
    (hY : Nonempty Y)
    (V : Γ → Matrix Y Y ℂ) (U : Γ → Matrix Y Y ℂ) (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hV : ∀ g : Γ, V g ∈ Matrix.unitaryGroup Y ℂ)
    (hU : ∀ a ∈ S, U a ∈ Matrix.unitaryGroup Y ℂ)
    (hcov : ∀ a ∈ S, ∀ g : Γ, V (a * g) = U a * V g * (U a)ᴴ)
    (g : Γ) :
    matMass (V g - V 1) ≤
      4 * WordMetric.wordNorm (S : Set Γ) g * generatorRankWeight V S := by
  have hm := displacementMass_le_four_mul_rank hY V hV g
  have hr := displacementRank_le_wordNorm_mul V U S hgen hU hcov g
  calc
    matMass (V g - V 1) ≤ 4 * (displacementRank V g : ℝ) := hm
    _ ≤ 4 * ((WordMetric.wordNorm (S : Set Γ) g *
          generatorRankWeight V S : ℕ) : ℝ) := by
      gcongr
    _ = 4 * WordMetric.wordNorm (S : Set Γ) g * generatorRankWeight V S := by
      push_cast
      ring

end

end FinitePacketRankWeight
end GroupApproximation
