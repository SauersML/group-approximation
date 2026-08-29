import GroupApproximation.GGT.HullSCRelatorSeparation2Aligned

/-!
# The join: trivial connectors give the conjugation outright

The aligned case at `δ ≠ 0` looked like the hard one.  It is not, and no
aperiodicity is needed for it after all.

`GGT/OsinTheorem54SepFourGonMeet.lean` gives, for a matched block with trivial
connectors, that the two sides MEET: `p · vertex 1 q i · 1 = vertex 1 s j`,
where `p` is the four-gon's short first side -- which is the piece's own `y`.
That is not merely a coincidence of vertices; it pins `y` to the two prefixes,
`y · listVal (q.take i) = listVal (s.take j)`.  And the matched block already
puts the two members in step, `w.rotate i = w'.rotate j`
(`HullSC.rotate_eq_of_position_eq`).

Those two facts multiply out.  Writing `A` and `A'` for the two prefix values
and `V`, `V'` for what the two members name, `RelWord.listVal_rotate` turns the
rotation identity into `A⁻¹ V A = A'⁻¹ V' A'`, and `A' = y A` turns the right
side into `A⁻¹ (y⁻¹ V' y) A`.  Cancelling `A` leaves `V' = y V y⁻¹` -- **the
identity `RelWord.IsPiece` excludes, for the piece's own `y`**.

So the aligned case is not a centralizer claim after all: the closing clause
that `GGT/OsinTheorem54SepFourGonInterface.lean` refutes
(`fourGon_closing_clause_fails`) was never what this branch needed.  What it
needed was the *vertex* form rather than the segment form, and that the
connector `y` be the four-gon's own first side rather than an arbitrary short
element.  `GGT/HullSCRelatorSeparation2Centralizer.lean` records the equivalence
that made the danger visible; this module discharges it.

The general lemma mentions no relator: two words, a rotation identity, a vertex
identity, and the conjugation follows.  The relator enters only through
`HullSC.position_eq_of_alignedMatch`, which is what makes the rotation identity
available.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Join

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex is the basepoint times what the prefix spells.** -/
theorem vertex_eq_listVal_take (v : G) (l : List (GGT.RelLetter G Λ)) {i : ℕ}
    (hi : i ≤ l.length) :
    GGT.OsinComponents.vertex v l i = v * GGT.RelLetter.listVal (l.take i) := by
  have hlen : (l.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left hi]
  have hsplit := vertex_append_left v (l.take i) (l.drop i)
  rw [List.take_append_drop, hlen] at hsplit
  exact hsplit

/-- Conjugation by a common element cancels. -/
theorem conj_cancel {A X Y : G} (h : A⁻¹ * X * A = A⁻¹ * Y * A) : X = Y := by
  have h1 : A * (A⁻¹ * X * A) * A⁻¹ = A * (A⁻¹ * Y * A) * A⁻¹ := by rw [h]
  simpa [mul_assoc] using h1

/-- **Two words in step, with their prefixes related by `y`, name conjugate
elements -- conjugate by that same `y`.**

This is the whole aligned branch, and it mentions no relator: a rotation
identity and a vertex identity are all it uses. -/
theorem listVal_conj_of_rotate_eq_of_vertex_eq
    {l l' : List (GGT.RelLetter G Λ)} {i j : ℕ}
    (hi : i ≤ l.length) (hj : j ≤ l'.length) {y : G}
    (hrot : l.rotate i = l'.rotate j)
    (hy : y * GGT.OsinComponents.vertex (1 : G) l i
      = GGT.OsinComponents.vertex (1 : G) l' j) :
    GGT.RelLetter.listVal l' = y * GGT.RelLetter.listVal l * y⁻¹ := by
  rw [vertex_eq_listVal_take 1 l hi, vertex_eq_listVal_take 1 l' hj, one_mul,
    one_mul] at hy
  have e1 := RelWord.listVal_rotate l hi
  have e2 := RelWord.listVal_rotate l' hj
  have e3 : (GGT.RelLetter.listVal (l.take i))⁻¹ * GGT.RelLetter.listVal l
        * GGT.RelLetter.listVal (l.take i)
      = (GGT.RelLetter.listVal (l'.take j))⁻¹ * GGT.RelLetter.listVal l'
        * GGT.RelLetter.listVal (l'.take j) := by
    rw [← e1, ← e2, hrot]
  rw [← hy] at e3
  have e4 : (GGT.RelLetter.listVal (l.take i))⁻¹ * GGT.RelLetter.listVal l
        * GGT.RelLetter.listVal (l.take i)
      = (GGT.RelLetter.listVal (l.take i))⁻¹
        * (y⁻¹ * GGT.RelLetter.listVal l' * y)
        * GGT.RelLetter.listVal (l.take i) := by
    rw [e3, mul_inv_rev]
    simp [mul_assoc]
  have e5 : GGT.RelLetter.listVal l = y⁻¹ * GGT.RelLetter.listVal l' * y :=
    conj_cancel e4
  rw [e5]
  simp [mul_assoc]

end Join

section Relator

variable {G : Type u} [Group G]

/-- **The aligned case of step (c), closed.**

A matched block with trivial connectors, at any two offsets: the member of the
symmetrized closure that the piece points at is the conjugate of the other by
the piece's own connector, which is exactly what `RelWord.IsPiece` excludes.  No
constraint on the offsets is needed -- in particular none on `δ = j - i`, which
`GGT/OsinTheorem54SepFourGonMeet.lean` shows the quadrilateral cannot see. -/
theorem listVal_conj_of_alignedTrivial {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p h₀ h₁ ms).length)
    (hj : j < (relatorWord₂ p h₀ h₁ ms).length)
    {b b' : Bool} {e f : ℕ} (hef : e = f)
    (hx : ((relatorWord₂ p h₀ h₁ ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ e)))
    (hx' : ((relatorWord₂ p h₀ h₁ ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b' ((if b' then h₁ else h₀) ^ f)))
    {y : G}
    (hy : y * GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p h₀ h₁ ms).rotate c) i
      = GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p h₀ h₁ ms).rotate c') j) :
    GGT.RelLetter.listVal ((relatorWord₂ p h₀ h₁ ms).rotate c')
      = y * GGT.RelLetter.listVal ((relatorWord₂ p h₀ h₁ ms).rotate c) * y⁻¹ :=
  listVal_conj_of_rotate_eq_of_vertex_eq
    (by rw [List.length_rotate]; omega) (by rw [List.length_rotate]; omega)
    (rotate_eq_of_position_eq (relatorWord₂ p h₀ h₁ ms)
      (position_eq_of_alignedMatch hinj hnodup hi hj hef hx hx')) hy

end Relator

end HullSC
end GroupApproximation
