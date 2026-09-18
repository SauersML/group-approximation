import GroupApproximation.GGT.VanKampen.Estimating.Embedded

/-!
# Listing a filtered pocket boundary as `s₁ t₁⁻¹ s₂ t₂`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This is infrastructure for `thm:hull` in `non_mf_groups_exist.tex`
(around line 2121).

This file proves ingredient (2) of the rose planarity core
`GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement`, in list form.  Suppose a
region move keeps the darts of a boundary cycle `side₁ ++ A ++ side₂ ++ B` that satisfy `p`, the
kept darts in cycle order form a walk, and the kept part of each arc is again an arc.  Then the
kept darts are listed as `s₁ ++ A' ++ s₂ ++ B'`, where

* `s₁` and `s₂` are the kept darts of the old sides, so they are no longer than the old sides;
* `s₁` and `s₂` are walks;
* the three junctions `s₁ | A'`, `s₁ A' | s₂` and `s₁ A' s₂ | B'` meet at a vertex.

The kept part of an arc is an infix of the arc.  An infix of a cyclic arc is a cyclic arc
(`exists_infix_arc_of_le`, `exists_infix_arc_of_lt`).  Its start moves forward by the number of
dropped darts, and it wraps below the old start only when the new start passes the end of the
carrier list.  An empty kept part is a zero-length arc (`zeroArc`).

Everything here is unconditional.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

section Arcs

variable {Dart : Type v}

/-- The zero-length arc of a carrier list at a chosen base position. -/
def zeroArc {cycle : List Dart} (s : Fin (cycle.length + 1)) : CyclicArc cycle :=
  ⟨s, 0, Nat.zero_le _⟩

/-- A zero-length arc has no darts. -/
theorem zeroArc_darts {cycle : List Dart} (s : Fin (cycle.length + 1)) :
    (zeroArc s).darts = [] :=
  rfl

/-- An infix of the darts of an arc is an infix of the rotated carrier list. -/
theorem take_drop_darts_eq {cycle : List Dart} (t : CyclicArc cycle) {i j : ℕ}
    (hij : i + j ≤ t.length) :
    (t.darts.drop i).take j = (t.rotated.drop i).take j := by
  have hj : j ≤ t.length - i := by omega
  show ((t.rotated.take t.length).drop i).take j = (t.rotated.drop i).take j
  rw [List.drop_take, List.take_take, Nat.min_eq_left hj]

/-- **An infix of a cyclic arc is a cyclic arc** (no wrap past the end of the carrier list): its
start is the old start plus the number of dropped darts. -/
theorem exists_infix_arc_of_le {cycle : List Dart} (t : CyclicArc cycle) {i j : ℕ}
    (hij : i + j ≤ t.length) (hs : t.start.1 + i ≤ cycle.length) :
    ∃ t' : CyclicArc cycle, t'.start.1 = t.start.1 + i ∧ t'.length = j ∧
      t'.darts = (t.darts.drop i).take j := by
  have hlen := t.length_le
  refine ⟨⟨⟨t.start.1 + i, by omega⟩, j, by omega⟩, rfl, rfl, ?_⟩
  rw [take_drop_darts_eq t hij]
  show (cycle.drop (t.start.1 + i) ++ cycle.take (t.start.1 + i)).take j =
    ((cycle.drop t.start.1 ++ cycle.take t.start.1).drop i).take j
  have hi : i ≤ (cycle.drop t.start.1).length := by
    rw [List.length_drop]
    omega
  rw [List.drop_append_of_le_length hi, List.drop_drop]
  have h1 : j - (cycle.length - (t.start.1 + i)) ≤ t.start.1 + i := by omega
  have h2 : j - (cycle.length - (t.start.1 + i)) ≤ t.start.1 := by omega
  rw [List.take_append, List.take_append, List.take_take, List.take_take, List.length_drop,
    Nat.min_eq_left h1, Nat.min_eq_left h2]

/-- **An infix of a cyclic arc is a cyclic arc** (wrap past the end of the carrier list): its
start is the old start plus the number of dropped darts, minus the carrier length. -/
theorem exists_infix_arc_of_lt {cycle : List Dart} (t : CyclicArc cycle) {i j : ℕ}
    (hij : i + j ≤ t.length) (hs : cycle.length < t.start.1 + i) :
    ∃ t' : CyclicArc cycle, t'.start.1 = t.start.1 + i - cycle.length ∧ t'.length = j ∧
      t'.darts = (t.darts.drop i).take j := by
  have hlen := t.length_le
  have hst : t.start.1 ≤ cycle.length := by
    have := t.start.2
    omega
  refine ⟨⟨⟨t.start.1 + i - cycle.length, by omega⟩, j, by omega⟩, rfl, rfl, ?_⟩
  rw [take_drop_darts_eq t hij]
  show (cycle.drop (t.start.1 + i - cycle.length) ++
      cycle.take (t.start.1 + i - cycle.length)).take j =
    ((cycle.drop t.start.1 ++ cycle.take t.start.1).drop i).take j
  have hnil : (cycle.drop t.start.1).drop i = [] :=
    List.drop_eq_nil_of_le (by rw [List.length_drop]; omega)
  have hk : i - (cycle.drop t.start.1).length = t.start.1 + i - cycle.length := by
    rw [List.length_drop]
    omega
  rw [List.drop_append, hnil, List.nil_append, hk, List.drop_take, List.take_take]
  have h1 : min j (t.start.1 - (t.start.1 + i - cycle.length)) = j :=
    Nat.min_eq_left (by omega)
  have h2 : j ≤ (cycle.drop (t.start.1 + i - cycle.length)).length := by
    rw [List.length_drop]
    omega
  rw [h1, List.take_append_of_le_length h2]

/-- **An infix of a cyclic arc is a cyclic arc, not longer than the arc.** -/
theorem exists_infix_arc {cycle : List Dart} (t : CyclicArc cycle) {i j : ℕ}
    (hij : i + j ≤ t.length) :
    ∃ t' : CyclicArc cycle, t'.length = j ∧ t'.darts = (t.darts.drop i).take j := by
  by_cases hs : t.start.1 + i ≤ cycle.length
  · obtain ⟨t', _, hl, hd⟩ := exists_infix_arc_of_le t hij hs
    exact ⟨t', hl, hd⟩
  · obtain ⟨t', _, hl, hd⟩ := exists_infix_arc_of_lt t hij (by omega)
    exact ⟨t', hl, hd⟩

end Arcs

section Listing

/-- **The kept darts of a four-block cycle, block by block.**  If the kept darts of
`side₁ ++ A ++ side₂ ++ B` form a walk in cycle order, and the kept parts of `A` and `B` are
`A'` and `B'`, then the kept darts read `s₁ ++ A' ++ s₂ ++ B'` with walks `s₁`, `s₂` no longer than
the old sides, and the three junctions meet. -/
theorem exists_listing_of_filter {Dart : Type v} (R : Dart → Dart → Prop) (p : Dart → Bool)
    (side₁ A side₂ B A' B' : List Dart) (hA : A.filter p = A') (hB : B.filter p = B')
    (hchain : ((side₁ ++ A ++ side₂ ++ B).filter p).IsChain R) :
    ∃ s₁ s₂ : List Dart,
      s₁ ++ A' ++ s₂ ++ B' = (side₁ ++ A ++ side₂ ++ B).filter p ∧
      s₁.IsChain R ∧ s₂.IsChain R ∧
      (∀ a ∈ s₁.getLast?, ∀ b ∈ A'.head?, R a b) ∧
      (∀ a ∈ (s₁ ++ A').getLast?, ∀ b ∈ s₂.head?, R a b) ∧
      (∀ a ∈ (s₁ ++ A' ++ s₂).getLast?, ∀ b ∈ B'.head?, R a b) ∧
      s₁.length ≤ side₁.length ∧ s₂.length ≤ side₂.length := by
  have heq : side₁.filter p ++ A' ++ side₂.filter p ++ B' =
      (side₁ ++ A ++ side₂ ++ B).filter p := by
    rw [List.filter_append, List.filter_append, List.filter_append, hA, hB]
  refine ⟨side₁.filter p, side₂.filter p, heq, ?_⟩
  rw [← heq] at hchain
  obtain ⟨h123, _, hj₃⟩ := List.isChain_append.mp hchain
  obtain ⟨h12, hs₂, hj₂⟩ := List.isChain_append.mp h123
  obtain ⟨hs₁, _, hj₁⟩ := List.isChain_append.mp h12
  exact ⟨hs₁, hs₂, hj₁, hj₂, hj₃, List.length_filter_le _ _, List.length_filter_le _ _⟩

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- Filtering a reversed arc is reversing the filtered arc. -/
theorem filter_invDarts (X : DiscDiagram.{u, w, v} W) (p : X.toCombMap.Dart → Bool)
    (l : List X.toCombMap.Dart) :
    (invDarts X l).filter p = invDarts X (l.filter fun d => p (X.toCombMap.alpha d)) :=
  calc (invDarts X l).filter p = (l.reverse.map X.toCombMap.alpha).filter p := rfl
    _ = (l.reverse.filter (p ∘ X.toCombMap.alpha)).map X.toCombMap.alpha := List.filter_map
    _ = (l.filter (p ∘ X.toCombMap.alpha)).reverse.map X.toCombMap.alpha := by
      rw [List.filter_reverse]
    _ = invDarts X (l.filter fun d => p (X.toCombMap.alpha d)) := rfl

/-- **Ingredient (2) of the rose planarity core, in arc form.**  Let the boundary cycle be
`side₁ ++ t₁⁻¹ ++ side₂ ++ t₂` and let the move keep the darts satisfying `p`.  If the kept darts
form a walk in cycle order, the kept part of `t₁⁻¹` is `t₁'⁻¹` and the kept part of `t₂` is `t₂'`,
then the kept darts are listed as `s₁ t₁'⁻¹ s₂ t₂'` with walks `s₁`, `s₂` no longer than the old
sides and the three junctions meeting at a vertex. -/
theorem exists_junction_listing (X : DiscDiagram.{u, w, v} W)
    (R : X.toCombMap.Dart → X.toCombMap.Dart → Prop) (p : X.toCombMap.Dart → Bool)
    (side₁ side₂ : List X.toCombMap.Dart) {c₁ c₁' c₂ c₂' : List X.toCombMap.Dart}
    (t₁ : CyclicArc c₁) (t₁' : CyclicArc c₁') (t₂ : CyclicArc c₂) (t₂' : CyclicArc c₂')
    (hA : t₁.darts.filter (fun d => p (X.toCombMap.alpha d)) = t₁'.darts)
    (hB : t₂.darts.filter p = t₂'.darts)
    (hchain : ((side₁ ++ invDarts X t₁.darts ++ side₂ ++ t₂.darts).filter p).IsChain R) :
    ∃ s₁ s₂ : List X.toCombMap.Dart,
      s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts =
        (side₁ ++ invDarts X t₁.darts ++ side₂ ++ t₂.darts).filter p ∧
      s₁.IsChain R ∧ s₂.IsChain R ∧
      (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁'.darts).head?, R a b) ∧
      (∀ a ∈ (s₁ ++ invDarts X t₁'.darts).getLast?, ∀ b ∈ s₂.head?, R a b) ∧
      (∀ a ∈ (s₁ ++ invDarts X t₁'.darts ++ s₂).getLast?, ∀ b ∈ t₂'.darts.head?, R a b) ∧
      s₁.length ≤ side₁.length ∧ s₂.length ≤ side₂.length := by
  have hA' : (invDarts X t₁.darts).filter p = invDarts X t₁'.darts := by
    rw [filter_invDarts, hA]
  exact exists_listing_of_filter R p side₁ (invDarts X t₁.darts) side₂ t₂.darts
    (invDarts X t₁'.darts) t₂'.darts hA' hB hchain

end Listing

end GroupApproximation.Full.GL03C
