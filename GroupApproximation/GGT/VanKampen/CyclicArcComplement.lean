import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Complementary spans on a cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), for two regions `a`, `b` joining the same two
cells.  The pocket walk of the order `(a, b)` reads, on the carrier of a cell, an arc spanning the arc
of `a`, a gap, and the arc of `b`.  The walk of the order `(b, a)` reads an arc spanning the arc of
`b`, a gap, and the arc of `a`.  This file shows that the two gaps share no dart.

* `CyclicArc.rotate_eq_of_head?_eq_of_nodup`: two rotations of a list with no repeated element that
  start with the same element are equal.
* `CyclicArc.not_mem_of_complementary_spans`: on a cycle with no repeated dart, arcs reading
  `P ++ G₁ ++ Q` and `Q ++ G₂ ++ P`, with `P` and `Q` nonempty, have disjoint gaps `G₁` and `G₂`.
  The first arc gives a rotation `P G₁ Q Z₁` of the cycle; the rotation starting with `Q` is then
  `Q Z₁ P G₁`, and the second arc forces `G₂` to be `Z₁`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.CyclicArc

universe v

/-- **A rotation of a list with no repeated element is determined by its first element.** -/
theorem rotate_eq_of_head?_eq_of_nodup {α : Type*} {l : List α} (hl : l.Nodup) (hne : l ≠ [])
    {m₁ m₂ : ℕ} (h : (l.rotate m₁).head? = (l.rotate m₂).head?) : l.rotate m₁ = l.rotate m₂ := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hne
  have h₁ : m₁ % l.length < l.length := Nat.mod_lt _ hpos
  have h₂ : m₂ % l.length < l.length := Nat.mod_lt _ hpos
  rw [← List.rotate_mod l m₁, ← List.rotate_mod l m₂] at h ⊢
  rw [List.head?_rotate h₁, List.head?_rotate h₂, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂, Option.some_inj] at h
  rw [(hl.getElem_inj_iff).mp h]

/-- **Complementary spans have disjoint gaps.**  On a cycle with no repeated dart, let one arc read
`P ++ G₁ ++ Q` and another read `Q ++ G₂ ++ P`, with `P` and `Q` nonempty.  Then no dart of `G₁` is a
dart of `G₂`. -/
theorem not_mem_of_complementary_spans {Dart : Type v} {cycle : List Dart} (hcycle : cycle.Nodup)
    (A₁ A₂ : CyclicArc cycle) {P Q G₁ G₂ : List Dart} (hP : P ≠ []) (hQ : Q ≠ [])
    (h₁ : A₁.darts = P ++ G₁ ++ Q) (h₂ : A₂.darts = Q ++ G₂ ++ P) :
    ∀ x ∈ G₁, x ∉ G₂ := by
  intro x hx₁ hx₂
  have e₁ : A₁.darts = (cycle.rotate A₁.start.1).take A₁.length :=
    congrArg (List.take A₁.length) A₁.rotated_eq_rotate
  have e₂ : A₂.darts = (cycle.rotate A₂.start.1).take A₂.length :=
    congrArg (List.take A₂.length) A₂.rotated_eq_rotate
  have hsplit₁ : cycle.rotate A₁.start.1 =
      P ++ G₁ ++ Q ++ (cycle.rotate A₁.start.1).drop A₁.length := by
    rw [← h₁, e₁, List.take_append_drop]
  have hsplit₂ : cycle.rotate A₂.start.1 =
      Q ++ G₂ ++ P ++ (cycle.rotate A₂.start.1).drop A₂.length := by
    rw [← h₂, e₂, List.take_append_drop]
  obtain ⟨Z₁, hsplit₁⟩ : ∃ Z, cycle.rotate A₁.start.1 = P ++ G₁ ++ Q ++ Z := ⟨_, hsplit₁⟩
  obtain ⟨Z₂, hsplit₂⟩ : ∃ Z, cycle.rotate A₂.start.1 = Q ++ G₂ ++ P ++ Z := ⟨_, hsplit₂⟩
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  obtain ⟨q, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
  have hnd₁ : (p :: P' ++ G₁ ++ q :: Q' ++ Z₁).Nodup := by
    rw [← hsplit₁]
    exact List.nodup_rotate.mpr hcycle
  have hnd₂ : (q :: Q' ++ G₂ ++ p :: P').Nodup := by
    rw [← h₂]
    exact A₂.darts_nodup hcycle
  have hne : cycle ≠ [] := by
    have hp : p ∈ A₁.darts := by
      rw [h₁]
      simp
    exact List.ne_nil_of_mem (A₁.mem_cycle_of_mem_darts hp)
  -- The rotation of the cycle that starts with `q`, read from the first arc.
  have hrot₁ : cycle.rotate (A₁.start.1 + (p :: P' ++ G₁).length) =
      (q :: Q' ++ Z₁) ++ (p :: P' ++ G₁) := by
    rw [← List.rotate_rotate, hsplit₁]
    have e : p :: P' ++ G₁ ++ q :: Q' ++ Z₁ = (p :: P' ++ G₁) ++ (q :: Q' ++ Z₁) := by
      simp only [List.append_assoc]
    rw [e, List.rotate_append_length_eq]
  have heq : cycle.rotate (A₁.start.1 + (p :: P' ++ G₁).length) = cycle.rotate A₂.start.1 :=
    rotate_eq_of_head?_eq_of_nodup hcycle hne (by rw [hrot₁, hsplit₂]; rfl)
  rw [hrot₁, hsplit₂] at heq
  simp only [List.append_assoc, List.cons_append] at heq
  have heq' : Z₁ ++ p :: (P' ++ G₁) = G₂ ++ p :: (P' ++ Z₂) :=
    List.append_cancel_left (List.cons.inj heq).2
  rcases List.append_eq_append_iff.mp heq' with ⟨a', hG₂, hrest⟩ | ⟨c', hZ₁, -⟩
  · cases a' with
    | nil =>
      have hxZ : x ∈ Z₁ := by
        rw [hG₂, List.append_nil] at hx₂
        exact hx₂
      exact (List.nodup_append.mp hnd₁).2.2 x (by simp [hx₁]) x hxZ rfl
    | cons a₀ a'' =>
      simp only [List.cons_append, List.cons.injEq] at hrest
      have hpG₂ : p ∈ G₂ := by
        rw [hG₂, hrest.1]
        simp
      exact (List.nodup_append.mp hnd₂).2.2 p (by simp [hpG₂]) p (by simp) rfl
  · have hxZ : x ∈ Z₁ := by
      rw [hZ₁]
      exact List.mem_append_left _ hx₂
    exact (List.nodup_append.mp hnd₁).2.2 x (by simp [hx₁]) x hxZ rfl

end GroupApproximation.GGT.VanKampen.Embedded.CyclicArc

#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.rotate_eq_of_head?_eq_of_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.not_mem_of_complementary_spans
