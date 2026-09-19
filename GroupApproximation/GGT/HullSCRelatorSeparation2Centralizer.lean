import GroupApproximation.GGT.HullSCRelatorSeparation2Aligned

/-!
# What the aligned case really asks for

`HullSC.position_eq_of_alignedMatch` reduces the aligned case of step (c) to
`w.rotate i = w'.rotate j`, so that `w'` is a rotation of `w`.  At `i = j` the
two words are equal and `RelWord.IsPiece`'s clause `v' ≠ v` finishes.  At
`i ≠ j` the conclusion of the separation has to be proved, and this module says
exactly what proving it would mean.

`RelWord.listVal_rotate` names the value of a rotation: `w.rotate m` names
`P⁻¹ · V · P` for `V` the value of `w` and `P` the value of the prefix it moves.
So the identity the piece's exclusion clause denies,
`listVal w' = y · listVal w · y⁻¹`, is by `conj_rotate_iff` **equivalent to
`P · y` commuting with `V`**: the aligned case is a centralizer membership
statement about the piece's own `y`.

That is the same species as the claim that refuted the diagonal form of
`HullSC.RelatorSeparation`, and it is not available: nothing in the data
constrains `y` beyond its length, and the four-gon's `r = p⁻¹` -- which would
give it -- is itself equivalent to a centralizer claim and false in general.
So the aligned case at `i ≠ j` cannot be *proved*; it has to be made
*vacuous*, by a relator no nontrivial rotation of which matches it with short
connectors.

Recording the equivalence is what makes that visible, and it is what any route
through the case will consume: `conj_rotate_iff` turns "the piece is excluded"
into a commutation, where the design and the acylindricity of the action can
act on it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u w

section Centralizer

variable {G : Type u} [Group G]

/-- **Conjugating by a prefix, in commutation form.**  `P⁻¹ V P = y V y⁻¹`
exactly when `P y` commutes with `V`. -/
theorem conj_eq_conj_iff_commute (P V y : G) :
    P⁻¹ * V * P = y * V * y⁻¹ ↔ P * y * V = V * (P * y) := by
  constructor
  · intro h
    calc P * y * V = P * (y * V) := by rw [mul_assoc]
      _ = P * (y * V * y⁻¹ * y) := by rw [inv_mul_cancel_right]
      _ = P * (P⁻¹ * V * P * y) := by rw [h]
      _ = V * (P * y) := by simp [mul_assoc]
  · intro h
    have h2 : P * y * V * (P * y)⁻¹ = V := by
      rw [h]
      simp [mul_assoc]
    calc P⁻¹ * V * P = P⁻¹ * (P * y * V * (P * y)⁻¹) * P := by rw [h2]
      _ = y * V * y⁻¹ := by simp [mul_assoc]

/-- **The aligned case, as a commutation.**

The identity `RelWord.IsPiece` excludes holds for the rotation `w.rotate m`
exactly when the product of the moved prefix with the piece's own connector
commutes with what the relator names. -/
theorem conj_rotate_iff {Λ : Type w} {v : List (GGT.RelLetter G Λ)} {m : ℕ}
    (hm : m ≤ v.length) (y : G) :
    GGT.RelLetter.listVal (v.rotate m)
        = y * GGT.RelLetter.listVal v * y⁻¹
      ↔ GGT.RelLetter.listVal (v.take m) * y * GGT.RelLetter.listVal v
        = GGT.RelLetter.listVal v * (GGT.RelLetter.listVal (v.take m) * y) := by
  rw [RelWord.listVal_rotate v hm]
  exact conj_eq_conj_iff_commute _ _ y

/-- **At a trivial rotation the identity is free.**  The case `m = 0` is `w' = w`,
which `RelWord.IsPiece` excludes outright; recorded so that the split in the
assembly is visibly exhaustive. -/
theorem conj_rotate_zero {Λ : Type w} (v : List (GGT.RelLetter G Λ)) :
    GGT.RelLetter.listVal (v.rotate 0)
      = (1 : G) * GGT.RelLetter.listVal v * (1 : G)⁻¹ := by
  rw [List.rotate_zero, inv_one, mul_one, one_mul]

end Centralizer

end HullSC
end GroupApproximation
