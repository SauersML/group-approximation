import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.FaithfulCornerNormBridge

/-!
# The bounded Gram sequence of the corrected corner maps

The unchanged normal-Kazhdan proof uses the polar-corrected corner maps
`W_n(g)`.  In the formalized corner construction these are exactly
`PrintedCornerData.cornerMap n g`.  This file packages their Gram elements as
one bounded matrix sequence.  Boundedness is structural: each corrected map
already gives a bounded unitary sequence, and the numerator algebra is closed
under subtraction, star, multiplication, and finite sums.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Matrix PrintedCornerCompression
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]
variable {model : ℕ → FiniteModel}

noncomputable instance correctedCornerGramModelNonempty
    (D : PrintedCornerData G model) (n : ℕ) : Nonempty (D.cornerModel n) :=
  Fintype.card_pos_iff.mp (D.cornerModel_card_pos n)

/-- A fixed corrected corner map `g ↦ W_n(g)`, at every coordinate, as a
bounded matrix sequence. -/
def correctedCornerMapSequence (D : PrintedCornerData G model) (g : G) :
    BoundedMatrixSequence (fun n ↦ D.cornerModel n) :=
  ⟨fun n ↦ (D.cornerMap n g :
      Matrix (D.cornerModel n) (D.cornerModel n) ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact D.norm_cornerMap_le_one n g⟩⟩

@[simp]
theorem correctedCornerMapSequence_apply (D : PrintedCornerData G model)
    (g : G) (n : ℕ) :
    correctedCornerMapSequence D g n =
      (D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) := rfl

/-- The coordinate sequence
`b_n = ∑_{s∈S} (W_n(s)-1)ᴴ (W_n(s)-1)` from the printed proof.

This is a term of the bounded-sequence C-star algebra, rather than a raw
function accompanied by an assumed uniform bound. -/
def correctedCornerSectorGramSequence (D : PrintedCornerData G model)
    (S : Finset G) : BoundedMatrixSequence (fun n ↦ D.cornerModel n) :=
  ∑ s ∈ S,
    star (correctedCornerMapSequence D s - 1) *
      (correctedCornerMapSequence D s - 1)

/-- **Exact coordinate identity.**  The bounded sequence just constructed has
the literal Gram element of the actual polar-corrected corner maps in every
coordinate.  This is the `hbseq` input required by
`FaithfulCornerNormBridge`. -/
theorem correctedCornerSectorGramSequence_apply
    (D : PrintedCornerData G model) (S : Finset G) (n : ℕ) :
    correctedCornerSectorGramSequence D S n =
      sectorGram S (fun s ↦
        (D.cornerMap n s : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)) := by
  classical
  let ev : BoundedMatrixSequence (fun k ↦ D.cornerModel k) →+
      Matrix (D.cornerModel n) (D.cornerModel n) ℂ := {
    toFun a := a n
    map_zero' := rfl
    map_add' _ _ := rfl }
  change ev (∑ s ∈ S,
      star (correctedCornerMapSequence D s - 1) *
        (correctedCornerMapSequence D s - 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  change
    star ((correctedCornerMapSequence D s - 1) n) *
        ((correctedCornerMapSequence D s - 1) n) =
      ((D.cornerMap n s : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1)ᴴ *
        ((D.cornerMap n s : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1)
  rw [show (correctedCornerMapSequence D s - 1) n =
      (D.cornerMap n s : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1 by
        rfl]
  rw [Matrix.star_eq_conjTranspose]

/-- The exact existential form used when assembling the printed proof: the
required bounded representative exists and its coordinates are definitionally
the corrected-corner Gram elements. -/
theorem exists_correctedCornerSectorGramSequence
    (D : PrintedCornerData G model) (S : Finset G) :
    ∃ bseq : BoundedMatrixSequence (fun n ↦ D.cornerModel n),
      ∀ n, bseq n = sectorGram S (fun s ↦
        (D.cornerMap n s : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)) :=
  ⟨correctedCornerSectorGramSequence D S,
    correctedCornerSectorGramSequence_apply D S⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
