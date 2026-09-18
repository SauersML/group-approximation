import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Lobe
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# List and arc lemmas for the filtered lobe listing

Lane gl-p10-53.  Pure list facts used by `P10RoseLobe.FLBlock` to reduce
`roseLobe_FilterListingStatement` to a block statement.

* `roseLobeFL_isClosedDartWalk_excise`: cutting a closed sub-walk `B` out of a closed dart walk
  `A ++ B ++ C` leaves the closed dart walk `A ++ C`.
* `roseLobeFL_isClosedDartWalk_filter_of_block`: if a filter removes exactly one block of a closed
  dart walk (a linear block, or the complement of a linear block) and that block is closed, then
  the filtered walk is closed.
* `roseLobeFL_exists_arc_of_prefix_drop`, `roseLobeFL_exists_arc_of_infix`: a prefix of a tail of
  a cyclic arc is a cyclic arc inside the old window; an infix of a cyclic arc is a cyclic arc.
* `roseLobeFL_exists_arc_invDarts_of_infix`: an infix of `t⁻¹` for a cyclic arc `t` is `t₁⁻¹` for
  a cyclic arc `t₁`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- **Excising a closed sub-walk.**  If `A ++ B ++ C` and `B` are closed dart walks and `A ++ C`
is nonempty, then `A ++ C` is a closed dart walk. -/
theorem roseLobeFL_isClosedDartWalk_excise {M : CombMap.{v}} {A B C : List M.Dart}
    (hw : IsClosedDartWalk M (A ++ B ++ C)) (hB : IsClosedDartWalk M B) (hAC : A ++ C ≠ []) :
    IsClosedDartWalk M (A ++ C) := by
  have hrot : IsClosedDartWalk M (B ++ (C ++ A)) := by
    have h1 := IsClosedDartWalk.append_comm (P := A) (Q := B ++ C)
      (by rw [← List.append_assoc]; exact hw)
    rw [List.append_assoc] at h1
    exact h1
  obtain ⟨hBne, -, hBclose⟩ := hB
  have hCA : C ++ A ≠ [] := by
    intro h
    obtain ⟨hC, hA⟩ := List.append_eq_nil_iff.mp h
    exact hAC (by rw [hA, hC, List.nil_append])
  have hrot' := hrot
  obtain ⟨-, hchain, -⟩ := hrot'
  have hlink : M.vertexOf (M.alpha (B.getLast hBne)) = M.vertexOf ((C ++ A).head hCA) :=
    (List.isChain_append.mp hchain).2.2 (B.getLast hBne)
      (Option.mem_def.mpr (List.getLast?_eq_some_getLast hBne)) ((C ++ A).head hCA)
      (Option.mem_def.mpr (List.head?_eq_some_head hCA))
  exact (P10Rose.closedDartWalk_split hrot hBne hCA (hBclose.symm.trans hlink)).2.append_comm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_isClosedDartWalk_excise

/-- **A filter that removes one closed block keeps a closed walk.**  Let `c = A ++ B ++ C` be a
closed dart walk.  If the filter removes all of `B` and keeps all of the nonempty `A ++ C`, with
`B` empty or closed; or keeps all of the closed walk `B` and removes all of `A ++ C`; then the
filtered walk is closed. -/
theorem roseLobeFL_isClosedDartWalk_filter_of_block {M : CombMap.{v}} {p : M.Dart → Bool}
    {c A B C : List M.Dart} (hw : IsClosedDartWalk M c) (hc : c = A ++ B ++ C)
    (hblk : (B.filter p = [] ∧ (A ++ C).filter p = A ++ C ∧ A ++ C ≠ [] ∧
        (B = [] ∨ IsClosedDartWalk M B)) ∨
      (B.filter p = B ∧ (A ++ C).filter p = [] ∧ IsClosedDartWalk M B)) :
    IsClosedDartWalk M (c.filter p) := by
  subst hc
  rw [List.filter_append, List.filter_append]
  rcases hblk with ⟨hB, hAC, hne, hB'⟩ | ⟨hB, hAC, hBw⟩
  · rw [List.filter_append] at hAC
    rw [hB, List.append_nil, hAC]
    rcases hB' with rfl | hBw
    · rw [List.append_nil] at hw
      exact hw
    · exact roseLobeFL_isClosedDartWalk_excise hw hBw hne
  · rw [List.filter_append] at hAC
    obtain ⟨hA, hC⟩ := List.append_eq_nil_iff.mp hAC
    rw [hB, hA, hC, List.nil_append, List.append_nil]
    exact hBw

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_isClosedDartWalk_filter_of_block

/-- The darts of an explicit cyclic arc are a prefix of a rotation. -/
theorem roseLobeFL_darts_mk {α : Type v} {cyc : List α} {j m : ℕ} (hj : j < cyc.length + 1)
    (hm : m ≤ cyc.length) :
    (⟨⟨j, hj⟩, m, hm⟩ : CyclicArc cyc).darts = (cyc.rotate j).take m :=
  congrArg (List.take m) (CyclicArc.rotated_eq_rotate (⟨⟨j, hj⟩, m, hm⟩ : CyclicArc cyc))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_darts_mk

/-- A window of the darts of a cyclic arc is a prefix of a further rotation. -/
theorem roseLobeFL_take_drop_darts {α : Type v} {cyc : List α} (a : CyclicArc cyc) {k m : ℕ}
    (hkm : k + m ≤ a.length) :
    (a.darts.drop k).take m = ((cyc.rotate a.start.1).rotate k).take m := by
  have hal := a.length_le
  have h1 : m ≤ a.length - k := by omega
  have h2 : k ≤ (cyc.rotate a.start.1).length := by
    rw [List.length_rotate]
    omega
  have h3 : m ≤ ((cyc.rotate a.start.1).drop k).length := by
    rw [List.length_drop, List.length_rotate]
    omega
  rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate, List.drop_take, List.take_take,
    Nat.min_eq_left h1, List.rotate_eq_drop_append_take h2, List.take_append_of_le_length h3]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_take_drop_darts

/-- **A prefix of a tail of a cyclic arc is a cyclic arc in the old window.**  If `l` is a prefix
of the darts of `a` after the first `k`, and position `a.start + k` does not wrap, then `l` is the
darts of a cyclic arc `t` with `a.start ≤ t.start` and `t.start + t.length ≤ a.start + a.length`.
-/
theorem roseLobeFL_exists_arc_of_prefix_drop {α : Type v} {cyc : List α} (a : CyclicArc cyc)
    {k : ℕ} {l : List α} (hk : a.start.1 + k ≤ cyc.length) (hl : l <+: a.darts.drop k) :
    ∃ t : CyclicArc cyc, t.darts = l ∧ a.start.1 ≤ t.start.1 ∧
      t.start.1 + t.length ≤ a.start.1 + a.length := by
  have hlen := hl.length_le
  rw [List.length_drop, CyclicArc.darts_length] at hlen
  have hal := a.length_le
  by_cases hka : k ≤ a.length
  · have hkm : k + l.length ≤ a.length := by omega
    have hm : l.length ≤ cyc.length := by omega
    refine ⟨⟨⟨a.start.1 + k, by omega⟩, l.length, hm⟩, ?_, ?_, ?_⟩
    · rw [roseLobeFL_darts_mk, ← List.rotate_rotate, ← roseLobeFL_take_drop_darts a hkm]
      exact (List.prefix_iff_eq_take.mp hl).symm
    · show a.start.1 ≤ a.start.1 + k
      omega
    · show a.start.1 + k + l.length ≤ a.start.1 + a.length
      omega
  · have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨⟨a.start, 0, Nat.zero_le _⟩, ?_, ?_, ?_⟩
    · subst hl0
      exact List.take_zero
    · show a.start.1 ≤ a.start.1
      omega
    · show a.start.1 + 0 ≤ a.start.1 + a.length
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_exists_arc_of_prefix_drop

/-- **An infix of a cyclic arc is a cyclic arc.**  When the start of the infix wraps past the end
of the cycle, rotating by the length of the cycle is the identity. -/
theorem roseLobeFL_exists_arc_of_infix {α : Type v} {cyc : List α} (a : CyclicArc cyc)
    {l : List α} (hl : l <:+: a.darts) : ∃ t : CyclicArc cyc, t.darts = l := by
  obtain ⟨pre, suf, hsu⟩ := hl
  have hlen : pre.length + l.length ≤ a.length := by
    have h := congrArg List.length hsu
    simp only [List.length_append, CyclicArc.darts_length] at h
    omega
  have hl' : l <+: a.darts.drop pre.length :=
    ⟨suf, by rw [← hsu, List.append_assoc, List.drop_left]⟩
  by_cases hk : a.start.1 + pre.length ≤ cyc.length
  · obtain ⟨t, ht, -, -⟩ := roseLobeFL_exists_arc_of_prefix_drop a hk hl'
    exact ⟨t, ht⟩
  · have hs := a.start.2
    have hal := a.length_le
    have hm : l.length ≤ cyc.length := by omega
    have hper : cyc.rotate (a.start.1 + pre.length) =
        cyc.rotate (a.start.1 + pre.length - cyc.length) := by
      have h := List.rotate_rotate cyc cyc.length (a.start.1 + pre.length - cyc.length)
      have heq : cyc.length + (a.start.1 + pre.length - cyc.length) = a.start.1 + pre.length := by
        omega
      rw [List.rotate_length, heq] at h
      exact h.symm
    refine ⟨⟨⟨a.start.1 + pre.length - cyc.length, by omega⟩, l.length, hm⟩, ?_⟩
    rw [roseLobeFL_darts_mk, ← hper, ← List.rotate_rotate, ← roseLobeFL_take_drop_darts a hlen]
    exact (List.prefix_iff_eq_take.mp hl').symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_exists_arc_of_infix

/-- An infix of `invDarts X D` is `invDarts X l` for an infix `l` of `D`. -/
theorem roseLobeFL_exists_invDarts_of_infix {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    {D F : List X.toCombMap.Dart} (h : F <:+: invDarts X D) :
    ∃ l, l <:+: D ∧ invDarts X l = F := by
  refine ⟨(F.map X.toCombMap.alpha).reverse, ?_, ?_⟩
  · have h1 := (h.map X.toCombMap.alpha).reverse
    rw [invDarts, List.map_map, X.toCombMap.alpha_involutive.comp_self, List.map_id,
      List.reverse_reverse] at h1
    exact h1
  · rw [invDarts, List.reverse_reverse, List.map_map, X.toCombMap.alpha_involutive.comp_self,
      List.map_id]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_exists_invDarts_of_infix

/-- **An infix of `t⁻¹` is `t₁⁻¹`** for a cyclic arc `t₁` of the same cycle. -/
theorem roseLobeFL_exists_arc_invDarts_of_infix {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    {cyc : List X.toCombMap.Dart} (a : CyclicArc cyc) {F : List X.toCombMap.Dart}
    (h : F <:+: invDarts X a.darts) : ∃ t : CyclicArc cyc, F = invDarts X t.darts := by
  obtain ⟨l, hl, hinv⟩ := roseLobeFL_exists_invDarts_of_infix X h
  obtain ⟨t, ht⟩ := roseLobeFL_exists_arc_of_infix a hl
  exact ⟨t, by rw [ht, hinv]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_exists_arc_invDarts_of_infix

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
