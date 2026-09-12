import GroupApproximation.GGT.HullEeIsolated

/-!
# Closing a word into a cycle with one base letter

The isolated-component estimate is stated for a polygon, and
`OsinComponents.IsQuasiGeodesicPolygon` requires a CLOSED word --- `listVal = 1`.
The word Hull's Lemma `ee` starts from is not closed: it spells an element `h` of
`H_λ`.  Closing it costs exactly one letter, the base letter naming `h⁻¹`, and
this module builds that and proves the four things the estimate will read off it.

## Why the closing letter is a BASE letter, and why that matters twice

`h` lies in `H_λ`, hence in `⋃H_μ`, hence in `D_E`'s base --- `D_E` being the
reading in which the peripheral subgroups have been demoted to base letters and
`E` promoted to the family.  So the closing letter is admissible in `D_E` without
any hypothesis beyond the one the ball membership already carries.

That it is a base letter rather than a peripheral one is not bookkeeping.  It is
what will make the closure harmless to the component structure: a base letter is
never a component letter of any index, so appending it creates no component,
extends none, and --- this is the clause that matters --- cannot violate the
maximality clause of a component of the original word that runs all the way to
the end.  A word closed with a peripheral letter would merge with a trailing
component and the component count would change.

## What is here and what is next

Here: the construction, its length, the value it spells, the closure at
`(listVal u)⁻¹`, admissibility, and the agreement of vertices below the join.
That last is what lets isolation --- a statement about vertices --- be read on
either the open word or the cycle.

Next: that a component of `u` is a component of the cycle and conversely, which
is the argument sketched above, and with it the transport of
`isIsolated_transfer_of_minimal` from the open word to the polygon the estimate
consumes.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Cycle

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A word closed by one base letter.** -/
def cycleWord (u : List (RelLetter G Λ)) (x : G) : List (RelLetter G Λ) :=
  u ++ [RelLetter.base x]

omit [Group G] in
/-- **The closure costs one letter.**  The side count of the polygon the estimate
is applied to is this, not the length of the original word.

`cycleWord` appends and nothing else, so neither it nor its length carries the
group structure. -/
theorem length_cycleWord (u : List (RelLetter G Λ)) (x : G) :
    (cycleWord u x).length = u.length + 1 := by
  show (u ++ [RelLetter.base x]).length = _
  rw [List.length_append, List.length_singleton]

/-- **What the closed word spells.** -/
theorem listVal_cycleWord (u : List (RelLetter G Λ)) (x : G) :
    RelLetter.listVal (cycleWord u x) = RelLetter.listVal u * x := by
  show RelLetter.listVal (u ++ [RelLetter.base x]) = _
  rw [listVal_append, listVal_cons, RelLetter.listVal_nil, mul_one]
  rfl

/-- **The closure closes.**  At `x = (listVal u)⁻¹` the cycle spells the
identity, which is the clause `IsQuasiGeodesicPolygon` asks for. -/
theorem listVal_cycleWord_inv (u : List (RelLetter G Λ)) :
    RelLetter.listVal (cycleWord u (RelLetter.listVal u)⁻¹) = 1 := by
  rw [listVal_cycleWord, mul_inv_cancel]

/-- **The closed word is admissible** as soon as the closing letter lies in the
base --- which, at the point of use, it does: the element being spelled lies in a
peripheral subgroup, and `D_E`'s base contains every one of them. -/
theorem isLetter_cycleWord {D : RelGenSet G Λ} {u : List (RelLetter G Λ)}
    (hu : ∀ a ∈ u, D.IsLetter a) {x : G} (hx : x ∈ D.base) :
    ∀ a ∈ cycleWord u x, D.IsLetter a := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hu a h
  · rw [List.mem_singleton.mp h]
    exact hx

/-- **The cycle traces the original path below the join.**

Isolation is a statement about vertices, so this is what lets it be read on
either the open word or the closed one; above the join there is nothing to
compare, the original word having ended. -/
theorem vertex_cycleWord (u : List (RelLetter G Λ)) (x v : G) {i : ℕ}
    (hi : i ≤ u.length) : vertex v (cycleWord u x) i = vertex v u i := by
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take]
  show v * RelLetter.listVal ((u ++ [RelLetter.base x]).take i)
    = v * RelLetter.listVal (u.take i)
  rw [List.take_append_of_le_length hi]

end Cycle

end OsinComponents
end GGT
end GroupApproximation
