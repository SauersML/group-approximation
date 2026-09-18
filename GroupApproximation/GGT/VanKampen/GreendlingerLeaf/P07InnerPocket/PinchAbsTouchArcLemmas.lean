import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCutStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-77: list facts and the step lemma for the arc clauses

* `pinchAbsTouchArc_invInv`, `pinchAbsTouchArc_invAppend`, `pinchAbsTouchArc_mem_inv`: the
  reverse-orientation list `invDarts` is an involution, reverses appends, and has the reversed
  darts as members.
* `pinchAbsTouchArc_exists_idx`: an adjacent pair `x, y` of a rotation of `l` sits at cyclic
  positions `k, (k + 1) % l.length` of `l`.
* `pinchAbsTouchArc_step`: **one step of an enclosed outside walk.**  Let `x, y` be adjacent in a
  rotation of the walk `ow` of an `EnclosedFaceSetSucc`, on the same face.  Then
  `facePerm x = y`, unless `x` is pinched and `facePerm x` is not kept by `ow`.  The kept case is
  `PocketRun.succ_eq_facePerm_of_keep` and the pinch-free case is
  `PocketRun.succ_eq_facePerm_of_pinchFree`.
* `pinchAbsTouchArc_Run M G ow`: the residual predicate.  Every adjacent pair `x, y` of `ow` in `G`
  at a pinched dart `x` with `facePerm x` not kept has `facePerm x = y`.  If `ow` lies inside `G`,
  this is only asked of the adjacent pairs of one rotation of `ow`, so the wrap-around pair is
  allowed to jump.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- `invDarts` is an involution. -/
theorem pinchAbsTouchArc_invInv (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    invDarts X (invDarts X l) = l := by
  unfold invDarts
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  exact List.map_id'' (fun x => X.toCombMap.alpha_involutive x) l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_invInv

/-- `invDarts` reverses an append. -/
theorem pinchAbsTouchArc_invAppend (X : DiscDiagram.{u, w, v} W)
    (l₁ l₂ : List X.toCombMap.Dart) :
    invDarts X (l₁ ++ l₂) = invDarts X l₂ ++ invDarts X l₁ := by
  unfold invDarts
  rw [List.reverse_append, List.map_append]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_invAppend

/-- Membership in `invDarts`. -/
theorem pinchAbsTouchArc_mem_inv (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) : e ∈ invDarts X l ↔ X.toCombMap.alpha e ∈ l := by
  unfold invDarts
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [X.toCombMap.alpha_involutive y]
    exact List.mem_reverse.mp hy
  · intro he
    exact ⟨X.toCombMap.alpha e, List.mem_reverse.mpr he, X.toCombMap.alpha_involutive e⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_mem_inv

/-- Membership of a reversed dart in `invDarts`. -/
theorem pinchAbsTouchArc_alpha_mem_inv (X : DiscDiagram.{u, w, v} W)
    (l : List X.toCombMap.Dart) (d : X.toCombMap.Dart) :
    X.toCombMap.alpha d ∈ invDarts X l ↔ d ∈ l := by
  rw [pinchAbsTouchArc_mem_inv, X.toCombMap.alpha_involutive d]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_alpha_mem_inv

/-- **An adjacent pair of a rotation sits at cyclically adjacent positions.** -/
theorem pinchAbsTouchArc_exists_idx {α : Type*} {l : List α} {m : ℕ} {S Q : List α} {x y : α}
    (h : l.rotate m = S ++ x :: y :: Q) :
    ∃ (k : ℕ) (hk : k < l.length), l[k] = x ∧
      l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)) = y := by
  have h2 := List.rotate_append_length_eq S (x :: y :: Q)
  rw [← h, List.rotate_rotate] at h2
  have hlen : 2 ≤ l.length := by
    have h3 := congrArg List.length h
    simp only [List.length_rotate, List.length_append, List.length_cons] at h3
    omega
  have hL : 0 < l.length := by omega
  have hr0 : 0 < (l.rotate (m + S.length)).length := by rw [List.length_rotate]; omega
  have hr1 : 1 < (l.rotate (m + S.length)).length := by rw [List.length_rotate]; omega
  have hx : (l.rotate (m + S.length))[0] = x := List.getElem_of_eq h2 hr0
  have hy : (l.rotate (m + S.length))[1] = y := List.getElem_of_eq h2 hr1
  rw [List.getElem_rotate] at hx hy
  refine ⟨(m + S.length) % l.length, Nat.mod_lt _ hL, ?_, ?_⟩
  · exact (PocketRun.getElem_idx_congr l (by rw [Nat.zero_add]) _ _).trans hx
  · exact (PocketRun.getElem_idx_congr l
      (by rw [Nat.mod_add_mod, Nat.add_comm (m + S.length) 1]) _ _).trans hy

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_exists_idx

/-- **One step of an enclosed outside walk.**  Two darts adjacent in a rotation of `ow` and on the
same face follow the face permutation, unless the first is pinched and its face successor is not
kept by `ow`; in that residual case `hres` is used. -/
theorem pinchAbsTouchArc_step {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow) {m : ℕ} {S Q : List X.toCombMap.Dart}
    {x y : X.toCombMap.Dart} (h : ow.rotate m = S ++ x :: y :: Q)
    (hface : X.toCombMap.faceOf y = X.toCombMap.faceOf x)
    (hres : ¬ PocketRun.PinchFreeAt X.toCombMap x →
      ¬ walkKeep X.toCombMap ow (X.toCombMap.facePerm x) → X.toCombMap.facePerm x = y) :
    X.toCombMap.facePerm x = y := by
  obtain ⟨k, hk, hx, hy⟩ := pinchAbsTouchArc_exists_idx h
  by_cases hkeep : walkKeep X.toCombMap ow (X.toCombMap.facePerm x)
  · have h1 := PocketRun.succ_eq_facePerm_of_keep E k hk (by rw [hx]; exact hkeep)
    rw [hx, hy] at h1
    exact h1
  · by_cases hpf : PocketRun.PinchFreeAt X.toCombMap x
    · have h1 := PocketRun.succ_eq_facePerm_of_pinchFree E k hk (by rw [hx]; exact hpf)
        (by rw [hx, hy]; exact hface)
      rw [hx, hy] at h1
      exact h1
    · exact hres hpf hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_step

/-- **The residual predicate.**  (i) If some dart of `ow` is off `G`, every adjacent pair `x, y`
of `ow` (read cyclically) inside `G`, at a pinched `x` whose face successor is not kept by `ow`,
has `facePerm x = y`.  (ii) If `ow` lies inside `G`, some rotation of `ow` has this property for
all its (non-wrap-around) adjacent pairs. -/
def pinchAbsTouchArc_Run (M : CombMap.{v}) (G ow : List M.Dart) : Prop :=
  ((∃ e ∈ ow, e ∉ G) → ∀ (m : ℕ) (S Q : List M.Dart) (x y : M.Dart),
      ow.rotate m = S ++ x :: y :: Q → x ∈ G → y ∈ G → ¬ PocketRun.PinchFreeAt M x →
      ¬ walkKeep M ow (M.facePerm x) → M.facePerm x = y) ∧
  ((∀ e ∈ ow, e ∈ G) → ∃ n : ℕ, ∀ (S Q : List M.Dart) (x y : M.Dart),
      ow.rotate n = S ++ x :: y :: Q → ¬ PocketRun.PinchFreeAt M x →
      ¬ walkKeep M ow (M.facePerm x) → M.facePerm x = y)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_Run

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
