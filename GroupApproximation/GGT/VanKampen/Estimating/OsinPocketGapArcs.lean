import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# Gap arcs between two disjoint arcs of one cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Two distinct selected regions joining the
same cells `Π_i` and `Π_j` meet `∂Π_i` in two arcs with disjoint darts.  The pocket `Γ_1` between
the regions takes one of the two gaps between these arcs as its cell part `t_1`.  This module
proves the list-level part of that step:

* `CyclicArc.shorten` and `CyclicArc.shorten_darts`: the initial part of an arc;
* `CyclicArc.rest_darts`: the complementary arc is the rotated carrier after the arc;
* `CyclicArc.exists_gapArcs`: for two arcs with disjoint darts, the first nonempty, the carrier
  rotated to the start of the first arc is the first arc, a gap arc, the second arc and a second
  gap arc, and each gap arc starts where the arc before it ends.

No duplicate-free hypothesis is needed: two arcs that overlap as positions share a dart.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe v

namespace CyclicArc

/-- An entry of a list at an index below `m` lies among the first `m` entries. -/
theorem getElem_mem_take_of_lt {α : Type v} {l : List α} {i m : ℕ} (hi : i < l.length)
    (him : i < m) : l[i] ∈ l.take m := by
  have h : i < (l.take m).length := by
    rw [List.length_take]
    omega
  have hmem := List.getElem_mem h
  rwa [List.getElem_take] at hmem

/-- The initial part of an arc: the same start and a shorter length. -/
def shorten {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (m : ℕ)
    (hm : m ≤ arc.length) : CyclicArc cycle where
  start := arc.start
  length := m
  length_le := Nat.le_trans hm arc.length_le

/-- The darts of the initial part of length `m` are the first `m` darts of the arc. -/
theorem shorten_darts {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (m : ℕ)
    (hm : m ≤ arc.length) : (arc.shorten m hm).darts = arc.darts.take m := by
  show arc.rotated.take m = (arc.rotated.take arc.length).take m
  rw [List.take_take, Nat.min_eq_left hm]

/-- The complementary arc is the rotated carrier after the arc. -/
theorem rest_darts {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) :
    arc.rest.darts = arc.rotated.drop arc.length := by
  have h : arc.darts ++ arc.rest.darts = arc.darts ++ arc.rotated.drop arc.length := by
    rw [← arc.rotated_eq_darts_append_rest_darts, darts, List.take_append_drop]
  exact List.append_cancel_left h

/-- **Gap arcs.**  Two arcs of one carrier with disjoint darts, the first nonempty, split the
carrier rotated to the start of the first arc as the first arc, a gap arc starting where the
first arc ends, the second arc, and a gap arc starting where the second arc ends. -/
theorem exists_gapArcs {Dart : Type v} {cycle : List Dart} (X Y : CyclicArc cycle)
    (hX : 0 < X.length) (hXY : ∀ d ∈ X.darts, d ∉ Y.darts) :
    ∃ G₁ G₂ : CyclicArc cycle, G₁.start = X.rest.start ∧ G₂.start = Y.rest.start ∧
      X.rotated = X.darts ++ G₁.darts ++ Y.darts ++ G₂.darts := by
  obtain ⟨L, hL⟩ : ∃ L, L = X.rotated := ⟨_, rfl⟩
  have hLn : L.length = cycle.length := by rw [hL, X.rotated_length]
  have hxl : X.darts = L.take X.length := by rw [hL]; rfl
  have hXn : X.length ≤ L.length := by rw [hLn]; exact X.length_le
  have hrot : List.IsRotated L Y.rotated := by
    rw [hL, X.rotated_eq_rotate, Y.rotated_eq_rotate]
    exact (List.IsRotated.forall cycle X.start.1).trans
      (List.IsRotated.forall cycle Y.start.1).symm
  obtain ⟨r₀, hr₀⟩ := hrot
  obtain ⟨r, hr, hYr⟩ : ∃ r, r < L.length ∧ L.rotate r = Y.rotated :=
    ⟨r₀ % L.length, Nat.mod_lt _ (by omega), by rw [List.rotate_mod]; exact hr₀⟩
  have hyl : Y.darts = (L.rotate r).take Y.length := by rw [hYr]; rfl
  have hdr : (L.drop r).length = L.length - r := List.length_drop
  by_cases hy0 : Y.length = 0
  · have hY0 : Y.darts = [] := List.eq_nil_of_length_eq_zero (by rw [Y.darts_length, hy0])
    refine ⟨X.rest, Y.rest.shorten 0 (Nat.zero_le _), rfl, rfl, ?_⟩
    rw [hY0, shorten_darts, List.take_zero, List.append_nil, List.append_nil]
    exact X.rotated_eq_darts_append_rest_darts
  have hy : 0 < Y.length := Nat.pos_of_ne_zero hy0
  -- The second arc starts after the first arc.
  have hrx : X.length ≤ r := by
    by_contra hlt
    have h0 : 0 < (L.drop r).length := by omega
    have hmemX : (L.drop r)[0]'h0 ∈ X.darts := by
      rw [List.getElem_drop, hxl]
      exact getElem_mem_take_of_lt (by omega) (by omega)
    have hmemY : (L.drop r)[0]'h0 ∈ Y.darts := by
      have h := getElem_mem_take_of_lt (l := L.drop r ++ L.take r) (i := 0) (m := Y.length)
        (by rw [List.length_append]; omega) hy
      rw [List.getElem_append_left h0] at h
      rwa [hyl, List.rotate_eq_drop_append_take (Nat.le_of_lt hr)]
    exact hXY _ hmemX hmemY
  -- The second arc does not wrap past the end of the rotated carrier.
  have hry : r + Y.length ≤ L.length := by
    by_contra hgt
    have hL0 : 0 < L.length := by omega
    have hmemX : L[0]'hL0 ∈ X.darts := by
      rw [hxl]
      exact getElem_mem_take_of_lt hL0 hX
    have hmemY : L[0]'hL0 ∈ Y.darts := by
      rw [hyl, List.rotate_eq_drop_append_take (Nat.le_of_lt hr), List.take_append]
      apply List.mem_append_right
      rw [List.take_take]
      exact getElem_mem_take_of_lt hL0 (by omega)
    exact hXY _ hmemX hmemY
  have h₁ : r - X.length ≤ X.rest.length := by rw [rest_length]; omega
  have h₂ : L.length - r - Y.length ≤ Y.rest.length := by rw [rest_length]; omega
  refine ⟨X.rest.shorten (r - X.length) h₁, Y.rest.shorten (L.length - r - Y.length) h₂,
    rfl, rfl, ?_⟩
  have hdry : (L.drop (r + Y.length)).length = L.length - r - Y.length := by
    rw [List.length_drop]
    omega
  have hG₁ : (X.rest.shorten (r - X.length) h₁).darts =
      (L.drop X.length).take (r - X.length) := by
    rw [shorten_darts, rest_darts, hL]
  have hYd : Y.darts = (L.drop r).take Y.length := by
    rw [hyl, List.rotate_eq_drop_append_take (Nat.le_of_lt hr),
      List.take_append_of_le_length (by omega : Y.length ≤ (L.drop r).length)]
  have hG₂ : (Y.rest.shorten (L.length - r - Y.length) h₂).darts = L.drop (r + Y.length) := by
    rw [shorten_darts, rest_darts, ← hYr, List.rotate_eq_drop_append_take (Nat.le_of_lt hr),
      List.drop_append_of_le_length (by omega : Y.length ≤ (L.drop r).length), List.drop_drop,
      List.take_append_of_le_length (Nat.le_of_eq hdry.symm),
      List.take_of_length_le (Nat.le_of_eq hdry)]
  rw [← hL, hxl, hG₁, hYd, hG₂, ← List.take_add, Nat.add_sub_of_le hrx, ← List.take_add,
    List.take_append_drop]

end CyclicArc

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.getElem_mem_take_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.shorten_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.rest_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_gapArcs
