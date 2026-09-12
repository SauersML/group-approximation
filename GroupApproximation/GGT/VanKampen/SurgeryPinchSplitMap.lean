import GroupApproximation.GGT.VanKampen.VertexJoinMap
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a vertex at a pinch between two faces

Let `x ≠ y` be two darts at one vertex whose corners lie on distinct faces: the corner after `x` is
on the face of `alpha x` (since `facePerm (alpha x) = sigma x`), the corner after `y` on the face of
`alpha y`.  Composing the vertex rotation with the transposition of `x` and `y`
(`VertexJoin.toCombMap`, used here at two darts of ONE vertex) splits the vertex into two, and on
faces it is the right transposition of `alpha x` and `alpha y` (`VertexJoin.facePerm_eq`), which
merges the two faces into one.  Darts, edge reversal and labels are untouched.

* `vertexCount_eq`, `edgeCount_eq`, `faceCount_add_one`: one vertex more, the same edges, one face
  fewer.
* `connected`, `planar`: the old moves are still reachable, because `x`, `alpha x`, `alpha y`, `y`
  are joined along the merged face.
* `Cycles`: the two faces at the pinch, enumerated from their corners as `alpha x :: xs` and
  `alpha y :: ys` (the pattern of `EdgeDeletion.MergeCycles`); `exists_cycles`.
* `Cycles.isFaceCycle_merged`: the merged face is enumerated by `alpha x :: ys ++ alpha y :: xs`.
* `isFaceCycle_of_avoid`, `faceOf_eq_iff_of_avoid`: every other face keeps its enumeration and its
  darts.
* `Cycles.faceOf_merged_iff`: the darts of the merged face are the darts of the two old faces.
-/

namespace GroupApproximation.GGT.VanKampen.PinchSplit

open Equiv

universe u

/-- The last entry of a nonempty list with a given head, read through `getLast?`. -/
theorem getLast_cons_getD {α : Type u} (d : α) (l : List α) (h : d :: l ≠ []) :
    (d :: l).getLast h = l.getLast?.getD d :=
  Option.some.inj ((List.getLast?_eq_some_getLast h).symm.trans List.getLast?_cons)

/-- Darts on one face are joined by elementary moves. -/
theorem eqvGen_of_sameCycle_facePerm (N : CombMap.{u}) {d e : N.Dart}
    (h : N.facePerm.SameCycle d e) : Relation.EqvGen N.Adjacent d e := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : N.Dart), Relation.EqvGen N.Adjacent z ((N.facePerm ^ m) z) := by
    intro m
    induction m with
    | zero => intro z; exact Relation.EqvGen.refl _
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        have h1 : Relation.EqvGen N.Adjacent z (N.alpha z) :=
          Relation.EqvGen.rel _ _ (Or.inl rfl)
        have h2 : Relation.EqvGen N.Adjacent (N.alpha z) (N.facePerm z) :=
          Relation.EqvGen.rel _ _ (Or.inr rfl)
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h1 h2) (ih (N.facePerm z))
  simpa only [hn] using hpow n d

section Map

variable (M : CombMap.{u}) [DecidableEq M.Dart] (x y : M.Dart)

/-- **The split map**: the vertex rotation composed with the transposition of `x` and `y`. -/
abbrev toCombMap : CombMap.{u} := VertexJoin.toCombMap M x y

theorem facePerm_eq :
    (toCombMap M x y).facePerm = M.facePerm * Equiv.swap (M.alpha x) (M.alpha y) :=
  VertexJoin.facePerm_eq M x y

theorem facePerm_apply (d : M.Dart) :
    (toCombMap M x y).facePerm d = M.facePerm (Equiv.swap (M.alpha x) (M.alpha y) d) := by
  rw [facePerm_eq]
  rfl

theorem facePerm_apply_of_ne {d : M.Dart} (hx : d ≠ M.alpha x) (hy : d ≠ M.alpha y) :
    (toCombMap M x y).facePerm d = M.facePerm d := by
  rw [facePerm_apply, Equiv.swap_apply_of_ne_of_ne hx hy]

theorem facePerm_apply_alpha_left :
    (toCombMap M x y).facePerm (M.alpha x) = M.facePerm (M.alpha y) := by
  rw [facePerm_apply, Equiv.swap_apply_left]

theorem facePerm_apply_alpha_right :
    (toCombMap M x y).facePerm (M.alpha y) = M.facePerm (M.alpha x) := by
  rw [facePerm_apply, Equiv.swap_apply_right]

/-- **One vertex becomes two.** -/
theorem vertexCount_eq (hxy : M.sigma.SameCycle x y) (hne : x ≠ y) :
    (toCombMap M x y).vertexCount = M.vertexCount + 1 := by
  change Nat.card (CombMap.Orbit (M.sigma * Equiv.swap x y)) =
    Nat.card (CombMap.Orbit M.sigma) + 1
  rw [PermCycleCoordinates.orbit_card_mul_swap_eq]
  exact PermCycleCoordinates.orbit_card_swap_mul M.sigma x y hne hxy

/-- The edges are untouched. -/
theorem edgeCount_eq : (toCombMap M x y).edgeCount = M.edgeCount := rfl

/-- **Two faces become one.** -/
theorem faceCount_add_one (hface : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).faceCount + 1 = M.faceCount := by
  have h : Nat.card (CombMap.Orbit (M.facePerm * Equiv.swap (M.alpha x) (M.alpha y))) + 1 =
      Nat.card (CombMap.Orbit M.facePerm) := by
    rw [PermCycleCoordinates.orbit_card_mul_swap_eq]
    exact PermCycleCoordinates.orbit_card_swap_mul_of_not_sameCycle M.facePerm _ _ hface
  change Nat.card (CombMap.Orbit (toCombMap M x y).facePerm) + 1 =
    Nat.card (CombMap.Orbit M.facePerm)
  rw [facePerm_eq]
  exact h

/-- After splitting, `alpha x` and `alpha y` lie on one face. -/
theorem sameCycle_alpha (hface : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).facePerm.SameCycle (M.alpha x) (M.alpha y) := by
  have hconj : M.facePerm * Equiv.swap (M.alpha x) (M.alpha y) =
      Equiv.swap (M.alpha x) (M.alpha y) *
        (Equiv.swap (M.alpha x) (M.alpha y) * M.facePerm *
          (Equiv.swap (M.alpha x) (M.alpha y))⁻¹) := by
    rw [Equiv.swap_inv, ← mul_assoc, Equiv.swap_mul_self_mul]
  have hτ : ¬ (Equiv.swap (M.alpha x) (M.alpha y) * M.facePerm *
      (Equiv.swap (M.alpha x) (M.alpha y))⁻¹).SameCycle (M.alpha x) (M.alpha y) := by
    rw [Equiv.Perm.sameCycle_conj, Equiv.swap_inv, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact fun h => hface h.symm
  rw [facePerm_eq, hconj]
  exact PermCycleCoordinates.sameCycle_swap_mul_of_not_sameCycle _ _ _ hτ

/-- One old elementary move is reached in the split map. -/
theorem reachable_step (hface : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y))
    (u v : M.Dart) (huv : M.Adjacent u v) : Relation.EqvGen (toCombMap M x y).Adjacent u v := by
  have hjoin : Relation.EqvGen (toCombMap M x y).Adjacent x y := by
    have h1 : Relation.EqvGen (toCombMap M x y).Adjacent x (M.alpha x) :=
      Relation.EqvGen.rel _ _ (Or.inl rfl)
    have h2 : Relation.EqvGen (toCombMap M x y).Adjacent (M.alpha x) (M.alpha y) :=
      eqvGen_of_sameCycle_facePerm _ (sameCycle_alpha M x y hface)
    have h3 : Relation.EqvGen (toCombMap M x y).Adjacent (M.alpha y) y :=
      Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive y))
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h1 h2) h3
  rcases huv with h | h
  · exact Relation.EqvGen.rel _ _ (Or.inl h)
  · rw [← h]
    by_cases hux : u = x
    · rw [hux]
      have h1 : (toCombMap M x y).sigma y = M.sigma x := by
        change M.sigma (Equiv.swap x y y) = M.sigma x
        rw [Equiv.swap_apply_right]
      exact Relation.EqvGen.trans _ y _ hjoin (Relation.EqvGen.rel _ _ (Or.inr h1))
    · by_cases huy : u = y
      · rw [huy]
        have h2 : (toCombMap M x y).sigma x = M.sigma y := by
          change M.sigma (Equiv.swap x y x) = M.sigma y
          rw [Equiv.swap_apply_left]
        exact Relation.EqvGen.trans _ x _ (Relation.EqvGen.symm _ _ hjoin)
          (Relation.EqvGen.rel _ _ (Or.inr h2))
      · apply Relation.EqvGen.rel
        right
        change M.sigma (Equiv.swap x y u) = M.sigma u
        rw [Equiv.swap_apply_of_ne_of_ne hux huy]

/-- **Splitting at two distinct faces keeps the map connected.** -/
theorem connected (hM : M.IsConnected)
    (hface : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).IsConnected := by
  intro d e
  have hlift : ∀ u v : M.Dart, Relation.EqvGen M.Adjacent u v →
      Relation.EqvGen (toCombMap M x y).Adjacent u v := by
    intro u v huv
    induction huv with
    | rel u v h => exact reachable_step M x y hface u v h
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  exact hlift d e (hM d e)

/-- **Splitting at two distinct faces keeps the map planar.** -/
theorem planar (hM : M.IsPlanar) (hxy : M.sigma.SameCycle x y) (hne : x ≠ y)
    (hface : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).IsPlanar := by
  refine ⟨connected M x y hM.1 hface, ?_⟩
  have h := hM.2
  have hv := vertexCount_eq M x y hxy hne
  have hf := faceCount_add_one M x y hface
  unfold CombMap.eulerCharacteristic at h ⊢
  rw [edgeCount_eq]
  omega

/-- **Faces off the pinch keep their enumerations.** -/
theorem isFaceCycle_of_avoid {l : List M.Dart} (hl : M.IsFaceCycle l)
    (h₁ : M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (M.alpha x))
    (h₂ : M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (M.alpha y)) :
    (toCombMap M x y).IsFaceCycle l := by
  have hne : ∀ d ∈ l, d ≠ M.alpha x ∧ d ≠ M.alpha y := by
    intro d hd
    have hf := (hl.mem_iff d).mp hd
    exact ⟨fun h => h₁ (by rw [← hf, h]), fun h => h₂ (by rw [← hf, h])⟩
  refine ⟨hl.ne_nil, hl.nodup, ?_, ?_⟩
  · exact hl.chain.imp_of_mem_imp fun d e hd _ h => by
      show (toCombMap M x y).facePerm d = e
      rw [facePerm_apply_of_ne M x y (hne d hd).1 (hne d hd).2]
      exact h
  · have hlast := hne _ (List.getLast_mem hl.ne_nil)
    rw [facePerm_apply_of_ne M x y hlast.1 hlast.2]
    exact hl.closes

/-- **A dart off the two pinch faces keeps its face companions.** -/
theorem faceOf_eq_iff_of_avoid {d : M.Dart} (h₁ : M.faceOf d ≠ M.faceOf (M.alpha x))
    (h₂ : M.faceOf d ≠ M.faceOf (M.alpha y)) (e : M.Dart) :
    (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf d ↔ M.faceOf e = M.faceOf d := by
  obtain ⟨l, hl, hhead⟩ := M.exists_isFaceCycle_head d
  have hl' := isFaceCycle_of_avoid M x y hl (by rw [hhead]; exact h₁) (by rw [hhead]; exact h₂)
  have e₁ := hl.mem_iff e
  have e₂ := hl'.mem_iff e
  rw [hhead] at e₁ e₂
  exact e₂.symm.trans e₁

end Map

/-- **The two faces at the pinch**, each enumerated as a face cycle starting from its corner. -/
structure Cycles (M : CombMap.{u}) (x y : M.Dart) where
  /-- The face of `alpha x`, after `alpha x`. -/
  xs : List M.Dart
  /-- The face of `alpha y`, after `alpha y`. -/
  ys : List M.Dart
  cycX : M.IsFaceCycle (M.alpha x :: xs)
  cycY : M.IsFaceCycle (M.alpha y :: ys)
  /-- The two corners lie on distinct faces. -/
  face_ne : M.faceOf (M.alpha x) ≠ M.faceOf (M.alpha y)

/-- Two corners on distinct faces have enumerations. -/
theorem exists_cycles {M : CombMap.{u}} {x y : M.Dart}
    (hface : M.faceOf (M.alpha x) ≠ M.faceOf (M.alpha y)) : Nonempty (Cycles M x y) := by
  obtain ⟨l₁, hl₁, hh₁⟩ := M.exists_isFaceCycle_head (M.alpha x)
  obtain ⟨l₂, hl₂, hh₂⟩ := M.exists_isFaceCycle_head (M.alpha y)
  cases l₁ with
  | nil => exact absurd rfl hl₁.ne_nil
  | cons a xs =>
    cases l₂ with
    | nil => exact absurd rfl hl₂.ne_nil
    | cons b ys =>
      have ha : a = M.alpha x := hh₁
      have hb : b = M.alpha y := hh₂
      subst ha
      subst hb
      exact ⟨⟨xs, ys, hl₁, hl₂, hface⟩⟩

namespace Cycles

variable {M : CombMap.{u}} {x y : M.Dart} (C : Cycles M x y)

theorem not_sameCycle : ¬ M.facePerm.SameCycle (M.alpha x) (M.alpha y) :=
  fun h => C.face_ne ((M.faceOf_eq_iff _ _).mpr h)

theorem alpha_ne : M.alpha x ≠ M.alpha y := fun h => C.face_ne (by rw [h])

theorem ne : x ≠ y := fun h => C.face_ne (by rw [h])

theorem faceOf_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : M.faceOf d = M.faceOf (M.alpha x) :=
  (C.cycX.mem_iff d).mp (List.mem_cons_of_mem _ hd)

theorem faceOf_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) : M.faceOf d = M.faceOf (M.alpha y) :=
  (C.cycY.mem_iff d).mp (List.mem_cons_of_mem _ hd)

theorem ne_alpha_left_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : d ≠ M.alpha x := by
  rintro rfl
  exact (List.nodup_cons.mp C.cycX.nodup).1 hd

theorem ne_alpha_right_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : d ≠ M.alpha y := by
  rintro rfl
  exact C.face_ne (C.faceOf_of_mem_xs hd).symm

theorem ne_alpha_left_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) : d ≠ M.alpha x := by
  rintro rfl
  exact C.face_ne (C.faceOf_of_mem_ys hd)

theorem ne_alpha_right_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) : d ≠ M.alpha y := by
  rintro rfl
  exact (List.nodup_cons.mp C.cycY.nodup).1 hd

/-- The last dart of the face of `alpha x` returns to `alpha x`. -/
theorem facePerm_getD_last_xs : M.facePerm (C.xs.getLast?.getD (M.alpha x)) = M.alpha x := by
  have h := C.cycX.closes
  rw [getLast_cons_getD] at h
  exact h

/-- The last dart of the face of `alpha y` returns to `alpha y`. -/
theorem facePerm_getD_last_ys : M.facePerm (C.ys.getLast?.getD (M.alpha y)) = M.alpha y := by
  have h := C.cycY.closes
  rw [getLast_cons_getD] at h
  exact h

variable [DecidableEq M.Dart]

/-- **The merged face** is enumerated by `alpha x :: ys ++ alpha y :: xs`. -/
theorem isFaceCycle_merged :
    (toCombMap M x y).IsFaceCycle (M.alpha x :: C.ys ++ M.alpha y :: C.xs) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [List.cons_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, (List.nodup_cons.mp C.cycY.nodup).2,
      List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp C.cycX.nodup).2⟩, ?_⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact C.ne_alpha_left_of_mem_ys h rfl
      · rcases List.mem_cons.mp h with h | h
        · exact C.alpha_ne h
        · exact C.ne_alpha_left_of_mem_xs h rfl
    · intro h
      exact C.ne_alpha_right_of_mem_xs h rfl
    · intro d hd e he hde
      subst hde
      rcases List.mem_cons.mp he with h | h
      · exact C.ne_alpha_right_of_mem_ys hd h
      · exact C.face_ne ((C.faceOf_of_mem_xs h).symm.trans (C.faceOf_of_mem_ys hd))
  · refine List.IsChain.append ?_ ?_ ?_
    · rw [List.isChain_cons]
      refine ⟨fun w hw => ?_, ?_⟩
      · show (toCombMap M x y).facePerm (M.alpha x) = w
        rw [facePerm_apply_alpha_left]
        exact (List.isChain_cons.mp C.cycY.chain).1 w hw
      · exact (List.isChain_cons.mp C.cycY.chain).2.imp_of_mem_imp fun d e hd _ h => by
          show (toCombMap M x y).facePerm d = e
          rw [facePerm_apply_of_ne M x y (C.ne_alpha_left_of_mem_ys hd)
            (C.ne_alpha_right_of_mem_ys hd)]
          exact h
    · rw [List.isChain_cons]
      refine ⟨fun w hw => ?_, ?_⟩
      · show (toCombMap M x y).facePerm (M.alpha y) = w
        rw [facePerm_apply_alpha_right]
        exact (List.isChain_cons.mp C.cycX.chain).1 w hw
      · exact (List.isChain_cons.mp C.cycX.chain).2.imp_of_mem_imp fun d e hd _ h => by
          show (toCombMap M x y).facePerm d = e
          rw [facePerm_apply_of_ne M x y (C.ne_alpha_left_of_mem_xs hd)
            (C.ne_alpha_right_of_mem_xs hd)]
          exact h
    · intro u hu v hv
      have hu' : (M.alpha x :: C.ys).getLast? = some u := hu
      have hv' : (M.alpha y :: C.xs).head? = some v := hv
      rw [List.getLast?_cons] at hu'
      have hvb : M.alpha y = v := by simpa using hv'
      have hub : C.ys.getLast?.getD (M.alpha x) = u := Option.some.inj hu'
      subst hvb
      subst hub
      show (toCombMap M x y).facePerm (C.ys.getLast?.getD (M.alpha x)) = M.alpha y
      have hclose := C.facePerm_getD_last_ys
      cases hl : C.ys.getLast? with
      | none =>
        rw [hl, Option.getD_none] at hclose
        rw [Option.getD_none, facePerm_apply_alpha_left]
        exact hclose
      | some w =>
        rw [hl, Option.getD_some] at hclose
        have hw : w ∈ C.ys := List.mem_of_getLast? hl
        rw [Option.getD_some, facePerm_apply_of_ne M x y (C.ne_alpha_left_of_mem_ys hw)
          (C.ne_alpha_right_of_mem_ys hw)]
        exact hclose
  · rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), getLast_cons_getD]
    show (toCombMap M x y).facePerm (C.xs.getLast?.getD (M.alpha y)) = M.alpha x
    have hclose := C.facePerm_getD_last_xs
    cases hl : C.xs.getLast? with
    | none =>
      rw [hl, Option.getD_none] at hclose
      rw [Option.getD_none, facePerm_apply_alpha_right]
      exact hclose
    | some w =>
      rw [hl, Option.getD_some] at hclose
      have hw : w ∈ C.xs := List.mem_of_getLast? hl
      rw [Option.getD_some, facePerm_apply_of_ne M x y (C.ne_alpha_left_of_mem_xs hw)
        (C.ne_alpha_right_of_mem_xs hw)]
      exact hclose

/-- **The darts of the merged face** are the darts of the two old faces. -/
theorem faceOf_merged_iff (e : M.Dart) :
    (toCombMap M x y).faceOf e = (toCombMap M x y).faceOf (M.alpha x) ↔
      M.faceOf e = M.faceOf (M.alpha x) ∨ M.faceOf e = M.faceOf (M.alpha y) := by
  refine (C.isFaceCycle_merged.mem_iff e).symm.trans ?_
  rw [List.mem_append, List.mem_cons, List.mem_cons]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (by rw [h])
    · exact Or.inr (C.faceOf_of_mem_ys h)
    · exact Or.inr (by rw [h])
    · exact Or.inl (C.faceOf_of_mem_xs h)
  · rintro (h | h)
    · rcases List.mem_cons.mp ((C.cycX.mem_iff e).mpr h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases List.mem_cons.mp ((C.cycY.mem_iff e).mpr h) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl (Or.inr h')

/-- `alpha y` lies on the merged face. -/
theorem faceOf_alpha_right :
    (toCombMap M x y).faceOf (M.alpha y) = (toCombMap M x y).faceOf (M.alpha x) :=
  (C.faceOf_merged_iff (M.alpha y)).mpr (Or.inr rfl)

/-- **The split map of a planar map is planar.** -/
theorem planar (hM : M.IsPlanar) (hxy : M.sigma.SameCycle x y) : (toCombMap M x y).IsPlanar :=
  PinchSplit.planar M x y hM hxy C.ne C.not_sameCycle

theorem faceCount_add_one : (toCombMap M x y).faceCount + 1 = M.faceCount :=
  PinchSplit.faceCount_add_one M x y C.not_sameCycle

end Cycles

end GroupApproximation.GGT.VanKampen.PinchSplit

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.vertexCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.faceCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.connected
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.planar
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.isFaceCycle_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.faceOf_eq_iff_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.exists_cycles
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Cycles.isFaceCycle_merged
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Cycles.faceOf_merged_iff
