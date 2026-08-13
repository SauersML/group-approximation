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
  native_decide

theorem card_point : Fintype.card Point = 15 := by
  native_decide

theorem card_nonincidentFlag : Fintype.card NonincidentFlag = 120 := by
  native_decide

/-- Every point is outside exactly eight hyperplanes. -/
theorem nonincidence_row_count :
    ∀ p : Point, ∑ h : Point, nonincidenceEntry p h = 8 := by
  native_decide

/-- Two distinct points are simultaneously outside exactly four
hyperplanes. -/
theorem nonincidence_common_row_count :
    ∀ p q : Point, p ≠ q →
      ∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h = 4 := by
  native_decide

/-- Entrywise Gram identity for the nonincidence matrix:
`B Bᵀ = 4 I + 4 J`. -/
theorem nonincidence_gram_entry :
    ∀ p q : Point,
      (∑ h : Point, nonincidenceEntry p h * nonincidenceEntry q h) =
        if p = q then 8 else 4 := by
  native_decide

end NonincidentFlagGram
end GroupApproximation
