import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The loose count of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-24.

Write `σ` for the rotation and `α` for the reversal.  A passage `d → next d` of the pocket boundary
is *tight* when `σ (next d) = α d`, and *loose* otherwise.  The *loose count* of a pocket is the
number of its loose passages.

## Route

* `RegionMoveLooseDescentCount K`: the number of loose passages of `K`.
* `regionMoveLooseDescent_two_le_countP`, `regionMoveLooseDescent_three_le_countP` (proved): two,
  or three, distinct entries of a list that satisfy a predicate are counted.
* `regionMoveLooseDescent_two_le_count` (proved): two distinct loose passages give a count of at
  least `2`.
* `regionMoveLooseDescent_not_looseCross_of_count_le_one` (proved): a pocket with at most one loose
  passage has no loose crossing (through `regionMoveLoose_not_looseCross_of_subsingleton`).
* `regionMoveLooseDescent_three_le_count` (proved): a pocket in walk order with a loose crossing has
  loose count at least `3` (through `regionMoveLoose_three_of_looseCross`).

## Status

Everything here is proved.  The floor of the descent is `3`, not `1`: see the module
`RegionMoveLooseDescent`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

/-- **Two distinct entries satisfying a predicate are counted.** -/
theorem regionMoveLooseDescent_two_le_countP {β : Type*} {l : List β} (p : β → Bool) {a b : β}
    (ha : a ∈ l) (hb : b ∈ l) (hpa : p a = true) (hpb : p b = true) (hab : a ≠ b) :
    2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hnd : [a, b].Nodup := List.nodup_cons.mpr ⟨by simp [hab], List.nodup_singleton b⟩
  have hsub : [a, b] ⊆ l.filter p := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · rw [h]; exact List.mem_filter.mpr ⟨ha, hpa⟩
    · rw [h]; exact List.mem_filter.mpr ⟨hb, hpb⟩
  have hle := (List.Nodup.subperm hnd hsub).length_le
  simp only [List.length_cons, List.length_nil] at hle
  omega

/-- **Three distinct entries satisfying a predicate are counted.** -/
theorem regionMoveLooseDescent_three_le_countP {β : Type*} {l : List β} (p : β → Bool)
    {a b c : β} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) (hpa : p a = true) (hpb : p b = true)
    (hpc : p c = true) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hnd : [a, b, c].Nodup :=
    List.nodup_cons.mpr ⟨by simp [hab, hac],
      List.nodup_cons.mpr ⟨by simp [hbc], List.nodup_singleton c⟩⟩
  have hsub : [a, b, c] ⊆ l.filter p := by
    intro x hx
    simp at hx
    rcases hx with h | h | h
    · rw [h]; exact List.mem_filter.mpr ⟨ha, hpa⟩
    · rw [h]; exact List.mem_filter.mpr ⟨hb, hpb⟩
    · rw [h]; exact List.mem_filter.mpr ⟨hc, hpc⟩
  have hle := (List.Nodup.subperm hnd hsub).length_le
  simp only [List.length_cons, List.length_nil] at hle
  omega

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The loose count**: the number of passages `d → next d` of the pocket boundary that are not
tight. -/
noncomputable def RegionMoveLooseDescentCount (K : PocketFaceSet D eps X lo hi) : ℕ :=
  K.boundary.cycle.attach.countP (fun p => decide (¬RegionMoveCoreCloseTight K p.1 p.2))

/-- **Two distinct loose passages are counted.** -/
theorem regionMoveLooseDescent_two_le_count (K : PocketFaceSet D eps X lo hi)
    {e e' : X.toCombMap.Dart} (he : e ∈ K.boundary.cycle) (he' : e' ∈ K.boundary.cycle)
    (hne : e ≠ e') (hn : ¬RegionMoveCoreCloseTight K e he)
    (hn' : ¬RegionMoveCoreCloseTight K e' he') : 2 ≤ RegionMoveLooseDescentCount K := by
  unfold RegionMoveLooseDescentCount
  exact regionMoveLooseDescent_two_le_countP _ (List.mem_attach K.boundary.cycle ⟨e, he⟩)
    (List.mem_attach K.boundary.cycle ⟨e', he'⟩) (by simpa using hn) (by simpa using hn')
    (fun hh => hne (congrArg Subtype.val hh))

/-- **At most one loose passage leaves no loose crossing.** -/
theorem regionMoveLooseDescent_not_looseCross_of_count_le_one (K : PocketFaceSet D eps X lo hi)
    (h : RegionMoveLooseDescentCount K ≤ 1) : ¬RegionMoveCoreCloseLooseCross K := by
  apply regionMoveLoose_not_looseCross_of_subsingleton K
  intro e he e' he' hn hn'
  by_contra hne
  have h2 := regionMoveLooseDescent_two_le_count K he he' hne hn hn'
  omega

/-- **A loose crossing has loose count at least `3`**: the crossing pair and a third loose
passage. -/
theorem regionMoveLooseDescent_three_le_count (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (h : RegionMoveCoreCloseLooseCross K) :
    3 ≤ RegionMoveLooseDescentCount K := by
  obtain ⟨d₀, hd₀, d, hd, -, hnt₀, hne, hnt, -, -, e, he, hed₀, hed, hnte⟩ :=
    regionMoveLoose_three_of_looseCross K hK h
  unfold RegionMoveLooseDescentCount
  exact regionMoveLooseDescent_three_le_countP _ (List.mem_attach K.boundary.cycle ⟨d₀, hd₀⟩)
    (List.mem_attach K.boundary.cycle ⟨d, hd⟩) (List.mem_attach K.boundary.cycle ⟨e, he⟩)
    (by simpa using hnt₀) (by simpa using hnt) (by simpa using hnte)
    (fun hh => hne (congrArg Subtype.val hh).symm)
    (fun hh => hed₀ (congrArg Subtype.val hh).symm)
    (fun hh => hed (congrArg Subtype.val hh).symm)

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_two_le_countP
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_three_le_countP
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseDescentCount
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_two_le_count
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_not_looseCross_of_count_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_three_le_count
