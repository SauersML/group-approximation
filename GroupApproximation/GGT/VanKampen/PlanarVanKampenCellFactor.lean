import GroupApproximation.GGT.VanKampen.PlanarVanKampen
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell factors of a planar van Kampen product

The cellular form of the planar van Kampen lemma (`PlanarVanKampenCells`) records, for
each relator face, one factor of the boundary product: a signed conjugate of the word
read around that face (`CellFactor`).  This file holds the predicate and the list
bookkeeping of conjugating every factor.

* `CellFactor`, `CellFactor.conj`, `CellFactor.inv`, `CellFactor.of_isFaceCycle`.
* `prod_map_snd_conj`, `map_fst_conj`: conjugating the factors of a list conjugates
  their product and keeps their faces.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A cell factor**: a signed conjugate of the word read around a face. -/
def CellFactor (M : CombMap.{v}) (label : M.Dart → RelLetter G Lambda) (f : M.Face)
    (x : G) : Prop :=
  ∃ (l : List M.Dart) (hl : M.IsFaceCycle l) (c : G), M.faceOf (l.head hl.ne_nil) = f ∧
    (x = c * RelLetter.listVal (l.map label) * c⁻¹ ∨
      x = c * (RelLetter.listVal (l.map label))⁻¹ * c⁻¹)

namespace CellFactor

variable {M : CombMap.{v}} {label : M.Dart → RelLetter G Lambda} {f : M.Face} {x : G}

theorem conj (h : CellFactor M label f x) (d : G) : CellFactor M label f (d * x * d⁻¹) := by
  obtain ⟨l, hl, c, hf, hx | hx⟩ := h
  · exact ⟨l, hl, d * c, hf, Or.inl (by rw [hx]; group)⟩
  · exact ⟨l, hl, d * c, hf, Or.inr (by rw [hx]; group)⟩

theorem inv (h : CellFactor M label f x) : CellFactor M label f x⁻¹ := by
  obtain ⟨l, hl, c, hf, hx | hx⟩ := h
  · exact ⟨l, hl, c, hf, Or.inr (by rw [hx]; group)⟩
  · exact ⟨l, hl, c, hf, Or.inl (by rw [hx]; group)⟩

/-- The word of a face cycle is a cell factor of its face. -/
theorem of_isFaceCycle {l : List M.Dart} (hl : M.IsFaceCycle l) :
    CellFactor M label (M.faceOf (l.head hl.ne_nil)) (RelLetter.listVal (l.map label)) :=
  ⟨l, hl, 1, rfl, Or.inl (by group)⟩

end CellFactor

/-- Conjugating every factor conjugates the product. -/
theorem prod_map_snd_conj {α : Type*} (T : G) :
    ∀ factors : List (α × G),
      ((factors.map fun y => (y.1, T * y.2 * T⁻¹)).map Prod.snd).prod =
        T * (factors.map Prod.snd).prod * T⁻¹
  | [] => by simp
  | y :: ys => by
      simp only [List.map_cons, List.prod_cons, prod_map_snd_conj T ys]
      group

/-- Conjugating every factor keeps the faces. -/
theorem map_fst_conj {α : Type*} (T : G) (factors : List (α × G)) :
    (factors.map fun y => (y.1, T * y.2 * T⁻¹)).map Prod.fst = factors.map Prod.fst := by
  rw [List.map_map]
  rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellFactor.conj
#audit_axioms GroupApproximation.GGT.VanKampen.prod_map_snd_conj
