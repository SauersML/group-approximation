import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlaceFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# Shared vertices of a filtered closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module proves the last clause of `RoseFilterStepStatement`
(module `P10Rose/InPlaceFilter`) from the others: when a closed dart walk and its filter by a
predicate `p` are both closed walks, and `p` removes some dart, then some kept dart shares its
vertex with some removed dart.

## The mathematics

Let `l` be a closed dart walk (`IsClosedDartWalk`: consecutive darts chain, the last ends where the
first starts) and suppose `l.filter p` is again a closed dart walk and `p y = false` for some
`y ∈ l`.  Since `l.filter p ≠ []`, some dart has `p = true`.

1. *A true dart followed by a false dart* (`exists_pair_of_head`, `exists_pair_of_getLast`).  If a
   list `a :: l` has a false member and `p a = true`, walk forward from `a`: the first false member
   has a true predecessor, so `a :: l = P ++ x :: z :: Q` with `p x = true`, `p z = false`.  If the
   list has a true member and ends in a false dart, walk backwards in the same way.
2. *A rotation ending in a true dart and starting with a false dart* (`exists_rotation`).  Write
   `l = a :: t`.  If the last dart is false, (1) gives `P ++ x :: z :: Q` and the rotation
   `(z :: Q) ++ (P ++ [x])` ends in `x` and starts with `z`.  If the last dart is true and `p a` is
   false, the list itself is such a rotation.  If both are true, (1) from the head gives the pair.
3. *The core step* (`exists_vertexOf_eq_head_of_filter`).  If `l` and `l.filter p` are closed
   walks and the last dart of `l` is true, then the last dart of `l.filter p` is the last dart of
   `l` (`List.getLast_filter_of_pos`).  Both walks close through it: `vertexOf (α last)` is the
   starting vertex of `l.head` and of `(l.filter p).head`.  So the true dart `(l.filter p).head`
   starts at the vertex of `l.head`.
4. *The shared vertex* (`exists_shared_vertex_of_filter`).  Rotating a closed walk keeps it closed
   (`IsClosedDartWalk.append_comm`), and filtering commutes with `++`, so the rotation of (2) and
   its filter are closed walks.  By (3) some true dart starts at the vertex of its head, which is a
   false dart.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe v

namespace FilterWalk

/-- **A true dart followed by a false one**, walking forward from a true head. -/
theorem exists_pair_of_head {α : Type*} (p : α → Bool) (a : α) (l : List α) (ha : p a = true)
    (hy : ∃ y ∈ a :: l, p y = false) :
    ∃ (P : List α) (x z : α) (Q : List α),
      a :: l = P ++ x :: z :: Q ∧ p x = true ∧ p z = false := by
  induction l generalizing a with
  | nil =>
    obtain ⟨y, hy, hpy⟩ := hy
    rw [List.mem_singleton] at hy
    rw [hy, ha] at hpy
    cases hpy
  | cons b l ih =>
    obtain ⟨y, hy, hpy⟩ := hy
    cases hb : p b with
    | false => exact ⟨[], a, b, l, rfl, ha, hb⟩
    | true =>
      have hy' : y ∈ b :: l := by
        rcases List.mem_cons.mp hy with h | h
        · rw [h, ha] at hpy
          cases hpy
        · exact h
      obtain ⟨P, x, z, Q, hPQ, hx, hz⟩ := ih b hb ⟨y, hy', hpy⟩
      exact ⟨a :: P, x, z, Q, by rw [hPQ, List.cons_append], hx, hz⟩

/-- **A true dart followed by a false one**, walking backwards from a false last dart. -/
theorem exists_pair_of_getLast {α : Type*} (p : α → Bool) (a : α) (l : List α)
    (hx : ∃ x ∈ a :: l, p x = true)
    (hlast : p ((a :: l).getLast (List.cons_ne_nil a l)) = false) :
    ∃ (P : List α) (x z : α) (Q : List α),
      a :: l = P ++ x :: z :: Q ∧ p x = true ∧ p z = false := by
  induction l generalizing a with
  | nil =>
    obtain ⟨x, hx, hpx⟩ := hx
    rw [List.mem_singleton] at hx
    have ha : p a = false := hlast
    rw [hx, ha] at hpx
    cases hpx
  | cons b l ih =>
    have hlast' : p ((b :: l).getLast (List.cons_ne_nil b l)) = false := hlast
    cases ha : p a with
    | true =>
      cases hb : p b with
      | false => exact ⟨[], a, b, l, rfl, ha, hb⟩
      | true =>
        obtain ⟨P, x, z, Q, hPQ, hpx, hz⟩ := ih b ⟨b, List.mem_cons_self, hb⟩ hlast'
        exact ⟨a :: P, x, z, Q, by rw [hPQ, List.cons_append], hpx, hz⟩
    | false =>
      obtain ⟨x, hx, hpx⟩ := hx
      have hx' : x ∈ b :: l := by
        rcases List.mem_cons.mp hx with h | h
        · rw [h, ha] at hpx
          cases hpx
        · exact h
      obtain ⟨P, c, z, Q, hPQ, hpc, hz⟩ := ih b ⟨x, hx', hpx⟩ hlast'
      exact ⟨a :: P, c, z, Q, by rw [hPQ, List.cons_append], hpc, hz⟩

/-- **The rotation of a split pair**: `P ++ x :: z :: Q` rotates to `(z :: Q) ++ (P ++ [x])`,
which ends in `x` and starts with `z`. -/
theorem exists_rotation_of_pair {α : Type*} (p : α → Bool) {l : List α} (P : List α)
    (x z : α) (Q : List α) (hl : l = P ++ x :: z :: Q) (hx : p x = true) (hz : p z = false) :
    ∃ (A B : List α) (hne : B ++ A ≠ []), l = A ++ B ∧
      p ((B ++ A).getLast hne) = true ∧ p ((B ++ A).head hne) = false := by
  refine ⟨P ++ [x], z :: Q,
    List.append_ne_nil_of_right_ne_nil (z :: Q)
      (List.append_ne_nil_of_right_ne_nil P (List.cons_ne_nil x [])),
    hl.trans (by simp), ?_, hz⟩
  rw [List.getLast_append_of_ne_nil _
      (List.append_ne_nil_of_right_ne_nil P (List.cons_ne_nil x [])),
    List.getLast_append_of_ne_nil _ (List.cons_ne_nil x []), List.getLast_singleton]
  exact hx

/-- **A rotation ending in a true dart and starting with a false dart.** -/
theorem exists_rotation {α : Type*} (p : α → Bool) {l : List α} {x y : α} (hx : x ∈ l)
    (hpx : p x = true) (hy : y ∈ l) (hpy : p y = false) :
    ∃ (A B : List α) (hne : B ++ A ≠ []), l = A ++ B ∧
      p ((B ++ A).getLast hne) = true ∧ p ((B ++ A).head hne) = false := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hy)
  cases hlast : p ((a :: t).getLast (List.cons_ne_nil a t)) with
  | false =>
    obtain ⟨P, c, z, Q, hl, hc, hz⟩ := exists_pair_of_getLast p a t ⟨x, hx, hpx⟩ hlast
    exact exists_rotation_of_pair p P c z Q hl hc hz
  | true =>
    cases ha : p a with
    | false => exact ⟨a :: t, [], List.cons_ne_nil a t, (List.append_nil _).symm, hlast, ha⟩
    | true =>
      obtain ⟨P, c, z, Q, hl, hc, hz⟩ := exists_pair_of_head p a t ha ⟨y, hy, hpy⟩
      exact exists_rotation_of_pair p P c z Q hl hc hz

/-- **The core step.**  If a closed dart walk ending in a kept dart filters to a closed dart walk,
some kept dart starts at the vertex of the head of the walk. -/
theorem exists_vertexOf_eq_head_of_filter {M : CombMap.{v}} (p : M.Dart → Bool)
    {l : List M.Dart} (hw : IsClosedDartWalk M l) (hf : IsClosedDartWalk M (l.filter p))
    (hne : l ≠ []) (hlast : p (l.getLast hne) = true) :
    ∃ x ∈ l, p x = true ∧ M.vertexOf x = M.vertexOf (l.head hne) := by
  obtain ⟨_, _, hclose⟩ := hw
  obtain ⟨hne₁, _, hclose₁⟩ := hf
  have hlast₁ : (l.filter p).getLast hne₁ = l.getLast hne :=
    List.getLast_filter_of_pos hne hlast
  have hx := List.mem_filter.mp (List.head_mem hne₁)
  refine ⟨(l.filter p).head hne₁, hx.1, hx.2, ?_⟩
  rw [← hclose₁, hlast₁]
  exact hclose

/-- Filtering commutes with rotating a closed dart walk. -/
theorem isClosedDartWalk_filter_append_comm {M : CombMap.{v}} (p : M.Dart → Bool)
    {A B : List M.Dart} (hf : IsClosedDartWalk M ((A ++ B).filter p)) :
    IsClosedDartWalk M ((B ++ A).filter p) := by
  rw [List.filter_append] at hf ⊢
  exact hf.append_comm

/-- **A kept dart sharing its vertex with a removed dart.**  If a closed dart walk and its filter
by `p` are closed dart walks, and `p` removes some dart, then some kept dart and some removed dart
start at one vertex. -/
theorem exists_shared_vertex_of_filter {M : CombMap.{v}} (p : M.Dart → Bool)
    {l : List M.Dart} (hw : IsClosedDartWalk M l) (hf : IsClosedDartWalk M (l.filter p))
    {y : M.Dart} (hy : y ∈ l) (hpy : p y = false) :
    ∃ x ∈ l, ∃ z ∈ l, p x = true ∧ p z = false ∧ M.vertexOf x = M.vertexOf z := by
  have hne₁ : l.filter p ≠ [] := by
    obtain ⟨h, -⟩ := hf
    exact h
  have hx := List.mem_filter.mp (List.head_mem hne₁)
  obtain ⟨A, B, hne, rfl, hlast, hhead⟩ := exists_rotation p hx.1 hx.2 hy hpy
  obtain ⟨x, hxBA, hpx, hv⟩ := exists_vertexOf_eq_head_of_filter p hw.append_comm
    (isClosedDartWalk_filter_append_comm p hf) hne hlast
  exact ⟨x, List.mem_append.mpr (List.mem_append.mp hxBA).symm, (B ++ A).head hne,
    List.mem_append.mpr (List.mem_append.mp (List.head_mem hne)).symm, hpx, hhead, hv⟩

end FilterWalk

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_pair_of_head
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_pair_of_getLast
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_rotation_of_pair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_rotation
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_vertexOf_eq_head_of_filter
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.isClosedDartWalk_filter_append_comm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_shared_vertex_of_filter
