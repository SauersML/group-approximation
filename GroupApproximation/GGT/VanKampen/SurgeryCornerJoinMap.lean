import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Joining two vertices at corners of one face

Let `x` and `y` be darts at distinct vertices whose corners lie on one face, enumerated from the
corner of `x` as `alpha x :: xs ++ alpha y :: ys` (`Cycle`).  Composing the vertex rotation with the
transposition of `x` and `y` (`VertexJoin.toCombMap`) joins the two vertices.  On faces it is the
right transposition of `alpha x` and `alpha y` (`VertexJoin.facePerm_eq`), which splits the face
through both corners.  This is the inverse of `PinchSplit`.  Darts, edge reversal and labels are
untouched.

* `sameCycle_mul_swap_iff`, `sigma_sameCycle_iff`, `vertexOf_eq_iff`: the vertices of the join are
  the old vertices, with the vertices of `x` and `y` made one.
* `isFaceCycle_cons_of_swap`: a face cycle `a :: s ++ b :: t` gives the face cycle `a :: t` when
  the successors of `a` and `b` are transposed.
* `Cycle.isFaceCycle_left`, `Cycle.isFaceCycle_right`: the two new faces are enumerated by
  `alpha x :: ys` and `alpha y :: xs`; `Cycle.faceOf_left_iff`, `Cycle.faceOf_right_iff`,
  `Cycle.left_ne_right`, `Cycle.faceOf_old_iff`: their darts are the darts of the old face.
* `Cycle.isFaceCycle_of_ne`, `Cycle.faceOf_eq_iff_of_ne`: every other face keeps its enumeration
  and its darts.
* `vertexCount_add_one`, `Cycle.faceCount_eq`, `Cycle.planar`: one vertex fewer, one face more, and
  planarity is kept.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CornerJoin

open Equiv

universe u

/-- **Joining two cycles.**  Composing a permutation with the transposition of two points in
distinct cycles makes exactly these two cycles one. -/
theorem sameCycle_mul_swap_iff {D : Type u} [Fintype D] [DecidableEq D] (p : Perm D) {a b : D}
    (hab : ¬ p.SameCycle a b) (z z' : D) :
    (p * Equiv.swap a b).SameCycle z z' ↔ p.SameCycle z z' ∨
      ((p.SameCycle a z ∨ p.SameCycle b z) ∧ (p.SameCycle a z' ∨ p.SameCycle b z')) := by
  have hjoin : (p * Equiv.swap a b).SameCycle a b := by
    have hconj : p * Equiv.swap a b =
        Equiv.swap a b * (Equiv.swap a b * p * (Equiv.swap a b)⁻¹) := by
      rw [Equiv.swap_inv, ← mul_assoc, Equiv.swap_mul_self_mul]
    have hτ : ¬ (Equiv.swap a b * p * (Equiv.swap a b)⁻¹).SameCycle a b := by
      rw [Equiv.Perm.sameCycle_conj, Equiv.swap_inv, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
      exact fun h => hab h.symm
    rw [hconj]
    exact PermCycleCoordinates.sameCycle_swap_mul_of_not_sameCycle _ a b hτ
  have hstep : ∀ w, (p * Equiv.swap a b).SameCycle w (p w) := by
    intro w
    by_cases hwa : w = a
    · rw [hwa]
      have h : (p * Equiv.swap a b) b = p a := by
        rw [Perm.mul_apply, Equiv.swap_apply_right]
      rw [← h]
      exact hjoin.apply_right
    · by_cases hwb : w = b
      · rw [hwb]
        have h : (p * Equiv.swap a b) a = p b := by
          rw [Perm.mul_apply, Equiv.swap_apply_left]
        rw [← h]
        exact hjoin.symm.apply_right
      · have h : (p * Equiv.swap a b) w = p w := by
          rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwa hwb]
        rw [← h]
        exact Perm.SameCycle.rfl.apply_right
  have hlift : ∀ z z', p.SameCycle z z' → (p * Equiv.swap a b).SameCycle z z' := by
    intro z z' h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    clear hn h
    induction n with
    | zero => exact Perm.SameCycle.rfl
    | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact ih.trans (hstep _)
  constructor
  · intro h
    have hinv : ∀ w, (p.SameCycle z w ∨ ((p.SameCycle a z ∨ p.SameCycle b z) ∧
        (p.SameCycle a w ∨ p.SameCycle b w))) →
        (p.SameCycle z ((p * Equiv.swap a b) w) ∨ ((p.SameCycle a z ∨ p.SameCycle b z) ∧
          (p.SameCycle a ((p * Equiv.swap a b) w) ∨
            p.SameCycle b ((p * Equiv.swap a b) w)))) := by
      intro w hw
      rw [Perm.mul_apply]
      by_cases hwa : w = a
      · rw [hwa, Equiv.swap_apply_left]
        refine Or.inr ⟨?_, Or.inr Perm.SameCycle.rfl.apply_right⟩
        rcases hw with hw | hw
        · rw [← hwa]
          exact Or.inl hw.symm
        · exact hw.1
      · by_cases hwb : w = b
        · rw [hwb, Equiv.swap_apply_right]
          refine Or.inr ⟨?_, Or.inl Perm.SameCycle.rfl.apply_right⟩
          rcases hw with hw | hw
          · rw [← hwb]
            exact Or.inr hw.symm
          · exact hw.1
        · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
          rcases hw with hw | ⟨hw₁, hw₂⟩
          · exact Or.inl hw.apply_right
          · exact Or.inr ⟨hw₁, hw₂.imp (fun h => h.apply_right) (fun h => h.apply_right)⟩
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    clear hn h
    induction n with
    | zero => exact Or.inl Perm.SameCycle.rfl
    | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hinv _ ih
  · rintro (h | ⟨hz, hz'⟩)
    · exact hlift z z' h
    · have ha : ∀ w, (p.SameCycle a w ∨ p.SameCycle b w) →
          (p * Equiv.swap a b).SameCycle a w := by
        rintro w (h | h)
        · exact hlift a w h
        · exact hjoin.trans (hlift b w h)
      exact (ha z hz).symm.trans (ha z' hz')

section Map

variable (M : CombMap.{u}) [DecidableEq M.Dart] (x y : M.Dart)

/-- **The joined map**: the vertex rotation composed with the transposition of `x` and `y`. -/
abbrev toCombMap : CombMap.{u} := VertexJoin.toCombMap M x y

/-- **The vertex rotation of the join.**  Two darts share a vertex of the join when they shared a
vertex before, or each lies at the vertex of `x` or at the vertex of `y`. -/
theorem sigma_sameCycle_iff (hxy : ¬ M.sigma.SameCycle x y) (z z' : M.Dart) :
    (toCombMap M x y).sigma.SameCycle z z' ↔ M.sigma.SameCycle z z' ∨
      ((M.sigma.SameCycle x z ∨ M.sigma.SameCycle y z) ∧
        (M.sigma.SameCycle x z' ∨ M.sigma.SameCycle y z')) :=
  sameCycle_mul_swap_iff M.sigma hxy z z'

/-- **The vertices of the join.** -/
theorem vertexOf_eq_iff (hxy : ¬ M.sigma.SameCycle x y) (z z' : M.Dart) :
    (toCombMap M x y).vertexOf z = (toCombMap M x y).vertexOf z' ↔
      M.vertexOf z = M.vertexOf z' ∨
        ((M.vertexOf x = M.vertexOf z ∨ M.vertexOf y = M.vertexOf z) ∧
          (M.vertexOf x = M.vertexOf z' ∨ M.vertexOf y = M.vertexOf z')) := by
  simp only [CombMap.vertexOf_eq_iff]
  exact sigma_sameCycle_iff M x y hxy z z'

/-- **Two distinct vertices become one.** -/
theorem vertexCount_add_one (hxy : ¬ M.sigma.SameCycle x y) :
    (toCombMap M x y).vertexCount + 1 = M.vertexCount :=
  VertexJoin.vertexCount_add_one M x y hxy

theorem facePerm_apply (d : M.Dart) :
    (toCombMap M x y).facePerm d = M.facePerm (Equiv.swap (M.alpha x) (M.alpha y) d) :=
  PinchSplit.facePerm_apply M x y d

theorem facePerm_apply_of_ne {d : M.Dart} (hx : d ≠ M.alpha x) (hy : d ≠ M.alpha y) :
    (toCombMap M x y).facePerm d = M.facePerm d :=
  PinchSplit.facePerm_apply_of_ne M x y hx hy

/-- **A face through two corners splits.**  If `a :: s ++ b :: t` is a face cycle and the join
transposes the successors of `a` and `b`, then `a :: t` is a face cycle of the join. -/
theorem isFaceCycle_cons_of_swap {a b : M.Dart} {s t : List M.Dart}
    (hswap : ∀ d, (toCombMap M x y).facePerm d = M.facePerm (Equiv.swap a b d))
    (hcyc : M.IsFaceCycle (a :: s ++ b :: t)) : (toCombMap M x y).IsFaceCycle (a :: t) := by
  have hnd : (a :: (s ++ b :: t)).Nodup := hcyc.nodup
  have hat : a ∉ t := fun h =>
    (List.nodup_cons.mp hnd).1 (List.mem_append_right s (List.mem_cons_of_mem b h))
  have hbt : (b :: t).Nodup :=
    List.Nodup.sublist (List.sublist_append_right s (b :: t)) (List.nodup_cons.mp hnd).2
  have hbt' : b ∉ t := (List.nodup_cons.mp hbt).1
  have hq : ∀ d ∈ t, (toCombMap M x y).facePerm d = M.facePerm d := by
    intro d hd
    have hda : d ≠ a := by
      rintro rfl
      exact hat hd
    have hdb : d ≠ b := by
      rintro rfl
      exact hbt' hd
    rw [hswap, Equiv.swap_apply_of_ne_of_ne hda hdb]
  have hbchain := List.isChain_cons.mp (List.IsChain.right_of_append hcyc.chain)
  refine ⟨List.cons_ne_nil a t, List.nodup_cons.mpr ⟨hat, (List.nodup_cons.mp hbt).2⟩, ?_, ?_⟩
  · rw [List.isChain_cons]
    refine ⟨fun w hw => ?_, hbchain.2.imp_of_mem_imp fun d e hd _ h => ?_⟩
    · show (toCombMap M x y).facePerm a = w
      rw [hswap, Equiv.swap_apply_left]
      exact hbchain.1 w hw
    · show (toCombMap M x y).facePerm d = e
      rw [hq d hd]
      exact h
  · rw [PinchSplit.getLast_cons_getD]
    have hclose := hcyc.closes
    rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), PinchSplit.getLast_cons_getD]
      at hclose
    show (toCombMap M x y).facePerm (t.getLast?.getD a) = a
    cases hl : t.getLast? with
    | none =>
      rw [hl, Option.getD_none] at hclose
      rw [Option.getD_none, hswap, Equiv.swap_apply_left]
      exact hclose
    | some w =>
      rw [hl, Option.getD_some] at hclose
      rw [Option.getD_some, hq w (List.mem_of_getLast? hl)]
      exact hclose

end Map

/-- **The face through both corners**, enumerated from the corner of `x`.  The corner of `y` cuts
the rest of the walk into `xs` and `ys`. -/
structure Cycle (M : CombMap.{u}) (x y : M.Dart) where
  /-- The darts after `alpha x` and before `alpha y`. -/
  xs : List M.Dart
  /-- The darts after `alpha y` and before `alpha x`. -/
  ys : List M.Dart
  cycle : M.IsFaceCycle (M.alpha x :: xs ++ M.alpha y :: ys)

namespace Cycle

variable {M : CombMap.{u}} {x y : M.Dart} (C : Cycle M x y)

/-- The same face, enumerated from the corner of `y`. -/
theorem cycle_right : M.IsFaceCycle (M.alpha y :: C.ys ++ M.alpha x :: C.xs) := by
  have h := C.cycle.rotate (M.alpha x :: C.xs).length
  rwa [List.rotate_append_length_eq] at h

include C in
theorem alpha_ne : M.alpha x ≠ M.alpha y := fun h =>
  (List.nodup_cons.mp (C.cycle.nodup : (M.alpha x :: (C.xs ++ M.alpha y :: C.ys)).Nodup)).1
    (List.mem_append_right _ (List.mem_cons.mpr (Or.inl h)))

include C in
theorem ne : x ≠ y := fun h => C.alpha_ne (by rw [h])

theorem alpha_right_not_mem_ys : M.alpha y ∉ C.ys := fun h =>
  (List.nodup_cons.mp (C.cycle_right.nodup : (M.alpha y :: (C.ys ++ M.alpha x :: C.xs)).Nodup)).1
    (List.mem_append_left _ h)

include C in
/-- Both corners lie on the face. -/
theorem faceOf_alpha_right : M.faceOf (M.alpha y) = M.faceOf (M.alpha x) :=
  (C.cycle.mem_iff (M.alpha y)).mp (List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl)))

include C in
theorem sameCycle : M.facePerm.SameCycle (M.alpha x) (M.alpha y) :=
  (M.faceOf_eq_iff _ _).mp C.faceOf_alpha_right.symm

variable [DecidableEq M.Dart]

/-- **The left face** is enumerated by `alpha x :: ys`. -/
theorem isFaceCycle_left : (toCombMap M x y).IsFaceCycle (M.alpha x :: C.ys) :=
  isFaceCycle_cons_of_swap M x y (fun d => facePerm_apply M x y d) C.cycle

/-- **The right face** is enumerated by `alpha y :: xs`. -/
theorem isFaceCycle_right : (toCombMap M x y).IsFaceCycle (M.alpha y :: C.xs) :=
  isFaceCycle_cons_of_swap M x y (fun d => by rw [facePerm_apply, Equiv.swap_comm]) C.cycle_right

/-- The darts of the left face. -/
theorem faceOf_left_iff (e : M.Dart) :
    (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf (M.alpha x) ↔
      e = M.alpha x ∨ e ∈ C.ys :=
  (C.isFaceCycle_left.mem_iff e).symm.trans List.mem_cons

/-- The darts of the right face. -/
theorem faceOf_right_iff (e : M.Dart) :
    (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf (M.alpha y) ↔
      e = M.alpha y ∨ e ∈ C.xs :=
  (C.isFaceCycle_right.mem_iff e).symm.trans List.mem_cons

include C in
/-- **The two new faces are distinct.** -/
theorem left_ne_right :
    (toCombMap M x y).faceOf (M.alpha x) ≠ (toCombMap M x y).faceOf (M.alpha y) := by
  intro h
  rcases (C.faceOf_left_iff (M.alpha y)).mp h.symm with h' | h'
  · exact C.alpha_ne h'.symm
  · exact C.alpha_right_not_mem_ys h'

include C in
/-- **The darts of the old face** are the darts of the two new faces. -/
theorem faceOf_old_iff (e : M.Dart) :
    M.faceOf e = M.faceOf (M.alpha x) ↔
      (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf (M.alpha x) ∨
        (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf (M.alpha y) := by
  rw [C.faceOf_left_iff, C.faceOf_right_iff]
  refine (C.cycle.mem_iff e).symm.trans ?_
  rw [List.mem_append, List.mem_cons, List.mem_cons]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)

include C in
/-- **A dart off the old face keeps its face companions.** -/
theorem faceOf_eq_iff_of_ne {d : M.Dart} (hd : M.faceOf d ≠ M.faceOf (M.alpha x)) (e : M.Dart) :
    (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf d ↔ M.faceOf e = M.faceOf d :=
  PinchSplit.faceOf_eq_iff_of_avoid M x y hd (by rw [C.faceOf_alpha_right]; exact hd) e

include C in
/-- **A face other than the old face keeps its enumeration.** -/
theorem isFaceCycle_of_ne {l : List M.Dart} (hl : M.IsFaceCycle l)
    (hne : M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (M.alpha x)) :
    (toCombMap M x y).IsFaceCycle l :=
  PinchSplit.isFaceCycle_of_avoid M x y hl hne (by rw [C.faceOf_alpha_right]; exact hne)

include C in
/-- **One face more.** -/
theorem faceCount_eq : (toCombMap M x y).faceCount = M.faceCount + 1 :=
  VertexJoin.faceCount_eq M x y C.alpha_ne C.sameCycle

include C in
/-- **Joining two distinct vertices of one face keeps a planar map planar.** -/
theorem planar (hM : M.IsPlanar) (hxy : ¬ M.sigma.SameCycle x y) : (toCombMap M x y).IsPlanar :=
  VertexJoin.planar M x y hM hxy C.alpha_ne C.sameCycle

end Cycle

end GroupApproximation.GGT.VanKampen.CornerJoin

#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.sameCycle_mul_swap_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.sigma_sameCycle_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.vertexOf_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.isFaceCycle_cons_of_swap
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.isFaceCycle_left
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.isFaceCycle_right
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.left_ne_right
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.faceOf_old_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Cycle.planar
