import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-40: list lemmas for the witness step

Lane gl-p07-40.  Pure list facts used by `WitnessCurveStepTurn.lean`.  Certifies no printed
sentence on its own.

* `witnessStep_rotate_of_rotate_inv`: a rotation of `l.reverse.map f`, for an involution `f`,
  is the reverse image of a rotation of `l`.  So a consecutive pair `(x, y)` of a rotation of the
  inverse walk comes from the consecutive pair `(f y, f x)` of a rotation of the walk.
* `witnessStep_map_reverse_adj`: the pair `(f y, f x)` consecutive in `L` gives the pair `(x, y)`
  consecutive in `L.reverse.map f`.
* `witnessStep_filter_adj`: a consecutive pair whose two entries pass a filter stays consecutive
  in the filtered list.
* `witnessStep_adj_append`, `witnessStep_adj_mid`, `witnessStep_forward_of_mem_append`: the
  shapes `u ++ x :: (v ++ y :: z)` of the forward disjunct of `StepNext`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section StepList

variable {β : Type*}

/-- **A rotation of the inverse list, read back on the list.** -/
theorem witnessStep_rotate_of_rotate_inv {f : β → β} (hf : Function.Involutive f)
    {l s t : List β} {n : ℕ} {x y : β} (h : (l.reverse.map f).rotate n = s ++ x :: y :: t) :
    l.rotate (l.length - n % l.length) =
      (t.map f).reverse ++ f y :: f x :: (s.map f).reverse := by
  have h1 : (l.reverse.rotate n).map f = s ++ x :: y :: t := by
    rw [List.map_rotate]
    exact h
  rw [List.rotate_reverse] at h1
  have key : ∀ r : List β, ((r.reverse.map f).map f).reverse = r := fun r => by
    rw [List.map_map, hf.comp_self, List.map_id, List.reverse_reverse]
  rw [← key (l.rotate (l.length - n % l.length)), h1]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_rotate_of_rotate_inv

/-- **A consecutive pair of a list, read on the inverse list.** -/
theorem witnessStep_map_reverse_adj {f : β → β} (hf : Function.Involutive f)
    {L p q : List β} {x y : β} (hL : L = p ++ f y :: f x :: q) :
    L.reverse.map f = (q.map f).reverse ++ x :: y :: (p.map f).reverse := by
  subst hL
  simp [hf x, hf y]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_map_reverse_adj

/-- **A consecutive pair of filtered entries stays consecutive in the filter.** -/
theorem witnessStep_filter_adj {P : β → Bool} {L A B : List β} {x y : β}
    (hL : L = A ++ x :: y :: B) (hx : x ∈ L.filter P) (hy : y ∈ L.filter P) :
    ∃ u z : List β, L.filter P = u ++ x :: y :: z := by
  refine ⟨A.filter P, B.filter P, ?_⟩
  rw [hL, List.filter_append, List.filter_cons_of_pos (List.mem_filter.mp hx).2,
    List.filter_cons_of_pos (List.mem_filter.mp hy).2]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_filter_adj

/-- **A consecutive pair in the first block is a forward step.** -/
theorem witnessStep_adj_append {L R u z : List β} {x y : β} (h : L = u ++ x :: y :: z) :
    L ++ R = u ++ x :: ([] ++ y :: (z ++ R)) := by
  subst h
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_adj_append

/-- **A consecutive pair in a middle block is a forward step.** -/
theorem witnessStep_adj_mid {P C Q u z : List β} {x y : β} (h : C = u ++ x :: y :: z) :
    P ++ C ++ Q = (P ++ u) ++ x :: ([] ++ y :: (z ++ Q)) := by
  subst h
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_adj_mid

/-- **An entry of the first part comes before an entry of the second part.** -/
theorem witnessStep_forward_of_mem_append {L R : List β} {x y : β} (hx : x ∈ L) (hy : y ∈ R) :
    ∃ u v z : List β, L ++ R = u ++ x :: (v ++ y :: z) := by
  obtain ⟨p, q, rfl⟩ := List.append_of_mem hx
  obtain ⟨r, s, rfl⟩ := List.append_of_mem hy
  exact ⟨p, q ++ r, s, by simp⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_forward_of_mem_append

end StepList

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
