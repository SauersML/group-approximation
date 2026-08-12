import GroupApproximation.Domination.FixedDimension

/-!
# Affine character defects and blockwise domination

The phase-insensitive defect `qπ(g)=1-|χπ(g)|²` is not affine under direct
sums.  The standard remedy is the affine Hilbert--Schmidt defect

`δπ(g)=1-Re χπ(g)`.

Conjugate doubling converts the former into the latter exactly.  Normalized
trace is dimension-weighted under direct sums, so affine defects are likewise
dimension-weighted.  This file formalizes the numerical block argument in a
form independent of the later unitary irreducible-decomposition theorem.

Complete reducibility of finite-dimensional unitary representations is
classical representation theory.  It receives all credit for the eventual
existence of the block decompositions consumed here; the lemma below records
only the domination consequence specific to this paper.
-/

namespace GroupApproximation

open scoped BigOperators

namespace FDUnitaryRepresentation

variable {G : Type*} [Group G]

/-- Affine normalized-character defect. -/
noncomputable def affineCharacterDefect
    (π : FDUnitaryRepresentation G) (g : G) : ℝ :=
  1 - (π.character g).re

theorem affineCharacterDefect_nonneg
    (π : FDUnitaryRepresentation G) (g : G) :
    0 ≤ π.affineCharacterDefect g := by
  have hsq : Complex.normSq (π.character g) ≤ 1 :=
    normSq_normTrace_le_one π.carrier (π.isUnitary g) π.nonempty
  have hreSq : (π.character g).re * (π.character g).re ≤
      Complex.normSq (π.character g) := Complex.re_sq_le_normSq _
  unfold affineCharacterDefect
  by_contra h
  have hre : 1 < (π.character g).re := by linarith
  nlinarith

/-- Conjugate doubling turns `qπ` into the affine defect exactly. -/
theorem affineCharacterDefect_conjugateDouble
    (π : FDUnitaryRepresentation G) (g : G) :
    π.conjugateDouble.affineCharacterDefect g = π.characterDefect g := by
  unfold affineCharacterDefect characterDefect
  rw [character_conjugateDouble]
  norm_num

end FDUnitaryRepresentation

variable (G : Type*) [Group G]

/-- Affine domination in one exact dimension. -/
def HasFDAffineDominationInDimension
    (d : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    Fintype.card π.carrier = d →
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r

/-- A finite family of unitary blocks whose affine defects average to those
of `π` with the correct dimension weights.  Later complete-reducibility code
will construct this structure from invariant irreducible summands. -/
structure AffineBlockDecomposition (π : FDUnitaryRepresentation G) where
  blocks : FiniteModel
  representation : blocks → FDUnitaryRepresentation G
  dimension_sum :
    (∑ j, Fintype.card (representation j).carrier) = Fintype.card π.carrier
  defect_eq_weighted : ∀ g : G,
    π.affineCharacterDefect g =
      ∑ j, (Fintype.card (representation j).carrier : ℝ) /
          Fintype.card π.carrier * (representation j).affineCharacterDefect g

/-- Every block in a decomposition has dimension at most `D`. -/
def AffineBlockDecomposition.DegreeBounded
    {π : FDUnitaryRepresentation G} (B : AffineBlockDecomposition G π)
    (D : ℕ) : Prop :=
  ∀ j, Fintype.card (B.representation j).carrier ≤ D

/-- A common affine domination constant for every block controls the whole
dimension-weighted direct sum. -/
theorem affineDomination_of_blockwise
    {R : Finset G} {w : G}
    (π : FDUnitaryRepresentation G) (B : AffineBlockDecomposition G π)
    (C : ℝ)
    (hblock : ∀ j, (B.representation j).affineCharacterDefect w ≤
      C * ∑ r ∈ R, (B.representation j).affineCharacterDefect r) :
    π.affineCharacterDefect w ≤ C * ∑ r ∈ R, π.affineCharacterDefect r := by
  classical
  rw [B.defect_eq_weighted w]
  calc
    (∑ j, (Fintype.card (B.representation j).carrier : ℝ) /
          Fintype.card π.carrier * (B.representation j).affineCharacterDefect w)
        ≤ ∑ j, (Fintype.card (B.representation j).carrier : ℝ) /
          Fintype.card π.carrier *
            (C * ∑ r ∈ R, (B.representation j).affineCharacterDefect r) := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left (hblock j) (by positivity)
    _ = C * ∑ r ∈ R, π.affineCharacterDefect r := by
      simp_rw [B.defect_eq_weighted, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Fixed-dimensional affine bounds combine over any bounded-degree block
decomposition, regardless of total dimension or multiplicity. -/
theorem affineDomination_of_boundedBlockDecomposition
    {D : ℕ} {R : Finset G} {w : G}
    (hfixed : ∀ d ≤ D, HasFDAffineDominationInDimension G d R w)
    (π : FDUnitaryRepresentation G) (B : AffineBlockDecomposition G π)
    (hB : B.DegreeBounded G D) :
    ∃ C : ℝ, 0 ≤ C ∧
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r := by
  classical
  let C : ℕ → ℝ := fun d ↦ if hd : d ≤ D then Classical.choose (hfixed d hd) else 0
  have hC : ∀ d ≤ D, 0 ≤ C d := by
    intro d hd
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).1
  have hdom : ∀ d, (hd : d ≤ D) → ∀ σ : FDUnitaryRepresentation G,
      Fintype.card σ.carrier = d →
        σ.affineCharacterDefect w ≤
          C d * ∑ r ∈ R, σ.affineCharacterDefect r := by
    intro d hd σ hσ
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).2 σ hσ
  let Cmax : ℝ := ∑ d ∈ Finset.range (D + 1), C d
  have hCmax : 0 ≤ Cmax := by
    unfold Cmax
    exact Finset.sum_nonneg fun d hd ↦ hC d
      (Nat.le_of_lt_succ (Finset.mem_range.mp hd))
  refine ⟨Cmax, hCmax, affineDomination_of_blockwise G π B Cmax ?_⟩
  intro j
  let d := Fintype.card (B.representation j).carrier
  have hd : d ≤ D := hB j
  have hdmem : d ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hCd : C d ≤ Cmax := by
    unfold Cmax
    exact Finset.single_le_sum
      (fun i hi ↦ hC i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hdmem
  exact (hdom d hd (B.representation j) rfl).trans
    (mul_le_mul_of_nonneg_right hCd
      (Finset.sum_nonneg fun r _ ↦
        (B.representation j).affineCharacterDefect_nonneg r))

end GroupApproximation
