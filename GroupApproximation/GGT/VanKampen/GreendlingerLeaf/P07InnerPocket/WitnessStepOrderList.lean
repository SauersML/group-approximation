import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistRotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-63: list facts on the strict order `WitnessStepGenusBefore`

Lane gl-p07-63.  Pure list lemmas for `WitnessStepOrderGenus.lean` and
`WitnessStepOrderStatement.lean`.  Certifies no printed sentence on its own.  NOT COMPILED:
authored without running Lean.

* `witnessStepOrder_before_iff_pair`: `c` before `d` in `L` iff `[c, d] <+ L`.
* `witnessStepOrder_before_asymm`: in a duplicate-free list the order is asymmetric.
* `witnessStepOrder_before_total`: two distinct entries are ordered one way or the other.
* `witnessStepOrder_before_sublist_iff`: a sublist of a duplicate-free list has, on its own
  entries, the order of the big list.
* `witnessStepOrder_rotate_sublist_trans`: a cyclic sublist of a cyclic sublist is a cyclic
  sublist (`L.rotate n <+ M`, `M.rotate k <+ w` give `L.rotate r <+ w`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

/-- **Order as a two-letter sublist.** -/
theorem witnessStepOrder_before_iff_pair {α : Type*} {L : List α} {c d : α} :
    WitnessStepGenusBefore L c d ↔ [c, d] <+ L := by
  constructor
  · rintro ⟨u, v, z, rfl⟩
    exact (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr (by simp))).trans
      (List.sublist_append_right u _)
  · intro h
    obtain ⟨r₁, r₂, rfl, hc, hd⟩ := List.cons_sublist_iff.mp h
    obtain ⟨u, v, rfl⟩ := List.append_of_mem hc
    obtain ⟨v', z, rfl⟩ := List.append_of_mem (List.singleton_sublist.mp hd)
    exact ⟨u, v ++ v', z, by simp⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_before_iff_pair

/-- **The order of a duplicate-free list is asymmetric.** -/
theorem witnessStepOrder_before_asymm {α : Type*} {L : List α} {c d : α} (hL : L.Nodup)
    (h : WitnessStepGenusBefore L c d) : ¬ WitnessStepGenusBefore L d c := by
  rintro ⟨u', v', z', h'⟩
  obtain ⟨u, v, z, h⟩ := h
  have hw : L = (u ++ c :: v) ++ d :: z := by
    rw [h]
    simp
  have hd : d ∈ u ++ c :: v := witnessStepPinchArc_mem_pre_of_before hL hw h' (by simp)
  have hsub : [d, d] <+ L := by
    rw [hw]
    exact (List.singleton_sublist.mpr hd).append (List.singleton_sublist.mpr (by simp))
  exact (List.nodup_cons.mp (hsub.nodup hL)).1 (by simp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_before_asymm

/-- **Two distinct entries are ordered.** -/
theorem witnessStepOrder_before_total {α : Type*} {L : List α} {c d : α} (hc : c ∈ L)
    (hd : d ∈ L) (hne : c ≠ d) :
    WitnessStepGenusBefore L c d ∨ WitnessStepGenusBefore L d c := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hc
  rw [List.mem_append, List.mem_cons] at hd
  rcases hd with hd | hd | hd
  · obtain ⟨u, v, rfl⟩ := List.append_of_mem hd
    exact Or.inr ⟨u, v, t, by simp⟩
  · exact absurd hd.symm hne
  · obtain ⟨v, z, rfl⟩ := List.append_of_mem hd
    exact Or.inl ⟨s, v, z, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_before_total

/-- **A sublist keeps the order of a duplicate-free list on its own entries.** -/
theorem witnessStepOrder_before_sublist_iff {α : Type*} {w L : List α} {c d : α}
    (hw : w.Nodup) (hL : L <+ w) (hc : c ∈ L) (hd : d ∈ L) :
    WitnessStepGenusBefore w c d ↔ WitnessStepGenusBefore L c d := by
  constructor
  · intro h
    by_cases hcd : c = d
    · subst hcd
      exact absurd h (witnessStepOrder_before_asymm hw h)
    · rcases witnessStepOrder_before_total hc hd hcd with h' | h'
      · exact h'
      · exact absurd h (witnessStepOrder_before_asymm hw
          (witnessStepOrder_before_iff_pair.mpr
            ((witnessStepOrder_before_iff_pair.mp h').trans hL)))
  · intro h
    exact witnessStepOrder_before_iff_pair.mpr ((witnessStepOrder_before_iff_pair.mp h).trans hL)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_before_sublist_iff

/-- **A cyclic sublist of a cyclic sublist is a cyclic sublist.**  Split `M` at `k`: the
rotation `M.rotate k` is `M₂ ++ M₁` for `M = M₁ ++ M₂`; the sublist `L.rotate n` of `M` splits
as `L₁ ++ L₂`, and `L₂ ++ L₁` is the rotation `L.rotate (n + |L₁|)`. -/
theorem witnessStepOrder_rotate_sublist_trans {α : Type*} {L M w : List α} {n k : ℕ}
    (h₁ : L.rotate n <+ M) (h₂ : M.rotate k <+ w) : ∃ r : ℕ, L.rotate r <+ w := by
  rw [List.rotate_eq_drop_append_take_mod] at h₂
  have h₁' : L.rotate n <+ M.take (k % M.length) ++ M.drop (k % M.length) := by
    rw [List.take_append_drop]
    exact h₁
  obtain ⟨L₁, L₂, hL, hL₁, hL₂⟩ := List.sublist_append_iff.mp h₁'
  refine ⟨n + L₁.length, ?_⟩
  rw [← List.rotate_rotate, hL, List.rotate_append_length_eq]
  exact (hL₂.append hL₁).trans h₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_rotate_sublist_trans

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
