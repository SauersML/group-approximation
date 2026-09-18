import Mathlib.Data.List.Nodup
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal Jordan: order of two members of a duplicate-free list

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-17.

The list lemma behind `Piece10Live/ExtremalJordan`: if a duplicate-free list is split
twice, `X ++ Y = U ++ V`, then no `e ∈ X` with `e ∈ V` can come together with a `b ∈ Y` with
`b ∈ U` (`extremalJordan_false_of_order`): the two splittings cannot put `e` before `b` and `b`
before `e` at once.

## Proof route

`List.append_eq_append_iff` splits `X ++ Y = U ++ V`.  Either `Y = p ++ V`, so `e ∈ Y` as well
as `e ∈ X`; or `X = U ++ q`, so `b ∈ X` as well as `b ∈ Y`.  Both contradict
`List.nodup_append`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

section Lists

variable {α : Type _}

/-- **Two splittings of a duplicate-free list cannot reverse the order of two members.** -/
theorem extremalJordan_false_of_order {X Y U V : List α} {e b : α}
    (hnd : (X ++ Y).Nodup) (h : X ++ Y = U ++ V) (he : e ∈ X) (hb : b ∈ Y)
    (hbU : b ∈ U) (heV : e ∈ V) : False := by
  have hdis := (List.nodup_append.mp hnd).2.2
  rcases List.append_eq_append_iff.mp h with ⟨p, _, hY⟩ | ⟨q, hX, _⟩
  · have heY : e ∈ Y := by
      rw [hY]
      exact List.mem_append_right p heV
    exact hdis e he e heY rfl
  · have hbX : b ∈ X := by
      rw [hX]
      exact List.mem_append_left q hbU
    exact hdis b hbX b hb rfl

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordan_false_of_order
