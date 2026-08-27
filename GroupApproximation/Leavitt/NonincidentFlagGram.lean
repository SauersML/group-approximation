import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The nonincident point--hyperplane flag Gram matrix over `F₂⁴`

Over `F₂`, every nonzero vector is its own projective representative.  This
file formalizes the finite counting geometry behind the atlas overlap
`diag(GL₃(F₂),1) < GL₄(F₂)`:

* there are 15 projective points;
* there are 120 nonincident point--hyperplane flags;
* every point is outside eight hyperplanes; and
* two distinct points are simultaneously outside four hyperplanes.

The last two statements are the entrywise identity `B Bᵀ = 4 I + 4 J` for
the 15-by-15 nonincidence matrix.
-/

namespace GroupApproximation
namespace NonincidentFlagGram

abbrev BitVector4 := Fin 4 → ZMod 2

def pairing (v w : BitVector4) : ZMod 2 :=
  ∑ i, v i * w i

abbrev Point := {v : BitVector4 // v ≠ 0}

abbrev NonincidentFlag :=
  {x : Point × Point // pairing x.1 x.2 = 1}

def nonincidenceEntry (p h : Point) : ℕ :=
  if pairing p h = 1 then 1 else 0

theorem card_bitVector4 : Fintype.card BitVector4 = 16 := by
  decide

theorem card_point : Fintype.card Point = 15 := by
  decide

/-- Every point is outside exactly eight hyperplanes. -/
theorem nonincidence_row_count :
    ∀ p : Point, ∑ h : Point, nonincidenceEntry p h = 8 := by
  intro p
  fin_cases p <;> decide

theorem card_nonincidentFlag : Fintype.card NonincidentFlag = 120 := by
  classical
  have fiber_card (p : Point) :
      Fintype.card {h : Point // pairing p h = 1} = 8 := by
    calc
      Fintype.card {h : Point // pairing p h = 1} =
          (Finset.univ.filter fun h : Point => pairing p h = 1).card :=
        Fintype.card_subtype _
      _ = ∑ h : Point, if pairing p h = 1 then 1 else 0 := by
        symm
        simp
      _ = 8 := by
        simpa [nonincidenceEntry] using nonincidence_row_count p
  calc
    Fintype.card NonincidentFlag =
        Fintype.card (Σ p : Point, {h : Point // pairing p h = 1}) := by
      exact Fintype.card_congr
        (Equiv.subtypeProdEquivSigmaSubtype fun p h : Point => pairing p h = 1)
    _ = ∑ p : Point, Fintype.card {h : Point // pairing p h = 1} :=
      Fintype.card_sigma
    _ = 120 := by simp [fiber_card]

private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem nonincidence_common_row_count_00 :
  ∀ p q : Point, p.1 0 = 0 → p.1 1 = 0 → p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  intro p q hp0 hp1
  fin_cases p <;> norm_num at hp0 hp1
  all_goals fin_cases q <;> decide

private theorem nonincidence_common_row_count_01 :
  ∀ p q : Point, p.1 0 = 0 → p.1 1 = 1 → p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  intro p q hp0 hp1
  fin_cases p <;> norm_num at hp0 hp1
  all_goals fin_cases q <;> decide

private theorem nonincidence_common_row_count_10 :
  ∀ p q : Point, p.1 0 = 1 → p.1 1 = 0 → p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  intro p q hp0 hp1
  fin_cases p <;> norm_num at hp0 hp1
  all_goals fin_cases q <;> decide

private theorem nonincidence_common_row_count_11 :
  ∀ p q : Point, p.1 0 = 1 → p.1 1 = 1 → p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  intro p q hp0 hp1
  fin_cases p <;> norm_num at hp0 hp1
  all_goals fin_cases q <;> decide

/-- Two distinct points are simultaneously outside exactly four
hyperplanes. -/
theorem nonincidence_common_row_count :
    ∀ p q : Point, p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  intro p q hpq
  rcases zmod2_eq_zero_or_one (p.1 0) with hp0 | hp0
  · rcases zmod2_eq_zero_or_one (p.1 1) with hp1 | hp1
    · exact nonincidence_common_row_count_00 p q hp0 hp1 hpq
    · exact nonincidence_common_row_count_01 p q hp0 hp1 hpq
  · rcases zmod2_eq_zero_or_one (p.1 1) with hp1 | hp1
    · exact nonincidence_common_row_count_10 p q hp0 hp1 hpq
    · exact nonincidence_common_row_count_11 p q hp0 hp1 hpq

/-- Entrywise Gram identity for the nonincidence matrix:
`B Bᵀ = 4 I + 4 J`. -/
theorem nonincidence_gram_entry :
    ∀ p q : Point,
      (∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h) =
        if p = q then 8 else 4 := by
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    rw [show (∑ h : Point, nonincidenceEntry p h * nonincidenceEntry p h) =
        ∑ h : Point, nonincidenceEntry p h by
      apply Finset.sum_congr rfl
      intro h _
      simp [nonincidenceEntry]]
    exact nonincidence_row_count p
  · rw [if_neg hpq]
    exact nonincidence_common_row_count p q hpq

end NonincidentFlagGram
end GroupApproximation
