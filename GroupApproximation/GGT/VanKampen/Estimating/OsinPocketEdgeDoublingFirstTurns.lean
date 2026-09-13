import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingInside
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# First-turn order survives the doubling of an edge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch step for a pocket face set in first-turn order (condition (b)
of the turn-condition ruling) first turns corners into `G`-digons by doubling an edge, outside the
face set (`PocketFaceSet.faceEdgeDoubling`, `Estimating/OsinPocketEdgeDoubling.lean`) or inside it
(`PocketFaceSet.faceEdgeDoublingInside`, `Estimating/OsinPocketEdgeDoublingInside.lean`), and then
splits a vertex.  Both doublings are known to keep walk order and repeated visits.  This module
shows that they keep first-turn order as well.

The doubling is an edge insertion `EdgeInsertion.toCombMap M a b` at the two distinct corners
`a = w_j` and `b = w_{j+1}` of the doubled face.  Its rotation inserts the new dart `some none`
just before `a` and the new dart `none` just before `b`:

* `EdgeInsertion.sigma_embed_apply`: the rotation of an old dart, dart by dart;
* `EdgeInsertion.exists_sigma_step_lift`: one old rotation step is one or two new steps, and the
  darts passed in between are new;
* `EdgeInsertion.exists_sigma_pow_lift`: the same for `k` steps.

The two new darts form one edge and neither is an image of an old dart, so they are off the edges
of every image walk (`EdgeInsertion.not_walkKeep_map_embed_none`, `_some_none`), while an old dart
is on the edges of the image walk exactly when it is on the edges of the walk
(`EdgeInsertion.walkKeep_map_embed_iff`).  So a first turn lifts, with the new darts inserted into
its rotation count (`EdgeInsertion.firstTurn_embed`), and so does the first-turn chain of a
boundary cycle (`EdgeInsertion.firstTurnChain_map_embed`).

* `PocketFaceSet.faceEdgeDoubling_firstTurnChain`: across the doubling outside the face set.
* `PocketFaceSet.faceEdgeDoublingInside_firstTurnChain`: across the doubling inside the face set.

The first-turn chain is stated inline, in the spelling of `firstTurnWalkPocketInputs` on the
complement walk `cycle.reverse.map alpha`.

## Model check

The only place a lifted turn can change is a rotation step into a corner.  When the old turn from
`e` passes the step `σ z = a`, the new rotation reads `z ↦ some none ↦ a`, which is one extra step
past `some none`.  Its reverse `none` is the other end of the new edge, and no old dart maps to
either, so the extra dart is not a keep dart and the turn is not cut short.  The same holds at `b`
with `none`.  Equal corners would put two new darts in a row, but `EdgeInsertion.corners_ne` rules
this out, because the second corner sits at index `1 < |∂f|`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u w v

namespace EdgeInsertion

/-- **The rotation after inserting an edge, on an old dart.**  The successor `a` is preceded by
the new dart `some none`, the successor `b` by the new dart `none`; every other successor is
kept. -/
theorem sigma_embed_apply {M : CombMap.{u}} [DecidableEq M.Dart] {a b : M.Dart} (hab : a ≠ b)
    (z : M.Dart) :
    (toCombMap M a b).sigma (embed M z) =
      if M.sigma z = a then some none else if M.sigma z = b then none else embed M (M.sigma z) := by
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some b)
    (some (some z)) = _
  rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_some]
  by_cases ha : M.sigma z = a
  · have hb : ¬ M.sigma z = b := fun h => hab (ha.symm.trans h)
    simp only [if_pos ha, if_neg hb, reduceCtorEq, if_false]
  · by_cases hb : M.sigma z = b
    · simp only [if_neg ha, if_pos hb, Option.some.injEq]
    · simp only [if_neg ha, if_neg hb, Option.some.injEq, embed]

/-- The new dart `none` is followed, in the rotation, by the corner `b`. -/
theorem sigma_none_apply {M : CombMap.{u}} (a b : M.Dart) :
    (toCombMap M a b).sigma none = embed M b := by
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some b) none =
    some (some b)
  exact PermOrbitInsert.insertBefore_none _ _

/-- **One old rotation step lifts** to one or two new steps, past new darts only. -/
theorem exists_sigma_step_lift {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b) (z : M.Dart) :
    ∃ m : ℕ, 0 < m ∧
      ((toCombMap M a b).sigma ^ m) (embed M z) = embed M (M.sigma z) ∧
      ∀ t, 0 < t → t < m →
        ((toCombMap M a b).sigma ^ t) (embed M z) = none ∨
          ((toCombMap M a b).sigma ^ t) (embed M z) = some none := by
  classical
  by_cases ha : M.sigma z = a
  · refine ⟨2, Nat.two_pos, ?_, fun t ht0 ht2 => ?_⟩
    · rw [pow_two, Perm.mul_apply, sigma_embed_apply hab, if_pos ha,
        GeodesicCollar.edgeInsertion_sigma_some_none hab, ha]
    · obtain rfl : t = 1 := by omega
      rw [pow_one, sigma_embed_apply hab, if_pos ha]
      exact Or.inr rfl
  · by_cases hb : M.sigma z = b
    · refine ⟨2, Nat.two_pos, ?_, fun t ht0 ht2 => ?_⟩
      · rw [pow_two, Perm.mul_apply, sigma_embed_apply hab, if_neg ha, if_pos hb,
          sigma_none_apply, hb]
      · obtain rfl : t = 1 := by omega
        rw [pow_one, sigma_embed_apply hab, if_neg ha, if_pos hb]
        exact Or.inl rfl
    · refine ⟨1, Nat.one_pos, ?_, fun t ht0 ht1 => absurd ht1 (by omega)⟩
      rw [pow_one, sigma_embed_apply hab, if_neg ha, if_neg hb]

/-- **An old rotation run lifts**: `k` old steps are `k' ≥ k` new steps, and every dart passed
strictly inside the new run is either a new dart or the image of a dart passed strictly inside
the old run. -/
theorem exists_sigma_pow_lift {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b) (x : M.Dart)
    (k : ℕ) :
    ∃ k' : ℕ, k ≤ k' ∧ (0 < k' → 0 < k) ∧
      ((toCombMap M a b).sigma ^ k') (embed M x) = embed M ((M.sigma ^ k) x) ∧
      ∀ t', 0 < t' → t' < k' →
        (∃ t, 0 < t ∧ t < k ∧
            ((toCombMap M a b).sigma ^ t') (embed M x) = embed M ((M.sigma ^ t) x)) ∨
          ((toCombMap M a b).sigma ^ t') (embed M x) = none ∨
          ((toCombMap M a b).sigma ^ t') (embed M x) = some none := by
  induction k with
  | zero =>
      refine ⟨0, le_refl 0, fun h => absurd h (lt_irrefl 0), ?_, fun t' _ ht' => absurd ht' (by omega)⟩
      rw [pow_zero, pow_zero, Perm.one_apply, Perm.one_apply]
  | succ k ih =>
      obtain ⟨k', hk, hpos, heq, hmid⟩ := ih
      obtain ⟨m, hm0, hmeq, hmmid⟩ := exists_sigma_step_lift hab ((M.sigma ^ k) x)
      refine ⟨m + k', by omega, fun _ => Nat.succ_pos k, ?_, fun t' ht'0 ht' => ?_⟩
      · rw [pow_add, Perm.mul_apply, heq, hmeq, pow_succ', Perm.mul_apply]
      · by_cases hlt : t' < k'
        · rcases hmid t' ht'0 hlt with ⟨t, ht0, htk, h⟩ | h
          · exact Or.inl ⟨t, ht0, by omega, h⟩
          · exact Or.inr h
        · obtain ⟨s, rfl⟩ : ∃ s, t' = s + k' := ⟨t' - k', by omega⟩
          have hs : s < m := by omega
          rw [pow_add, Perm.mul_apply, heq]
          rcases Nat.eq_zero_or_pos s with rfl | hspos
          · refine Or.inl ⟨k, hpos (by omega), Nat.lt_succ_self k, ?_⟩
            rw [pow_zero, Perm.one_apply]
          · exact Or.inr (hmmid s hspos hs)

/-- An old dart is on the edges of an image walk exactly when it is on the edges of the walk. -/
theorem walkKeep_map_embed_iff {M : CombMap.{u}} (a b : M.Dart) (c : List M.Dart) (z : M.Dart) :
    walkKeep (toCombMap M a b) (c.map (embed M)) (embed M z) ↔ walkKeep M c z := by
  change embed M z ∈ c.map (embed M) ∨ embed M (M.alpha z) ∈ c.map (embed M) ↔
    z ∈ c ∨ M.alpha z ∈ c
  rw [List.mem_map_of_injective (embed_injective M), List.mem_map_of_injective (embed_injective M)]

/-- The new dart `none` is off the edges of every image walk. -/
theorem not_walkKeep_map_embed_none {M : CombMap.{u}} (a b : M.Dart) (c : List M.Dart) :
    ¬ walkKeep (toCombMap M a b) (c.map (embed M)) none := by
  change ¬ (none ∈ c.map (embed M) ∨ some none ∈ c.map (embed M))
  simp [embed]

/-- The new dart `some none` is off the edges of every image walk. -/
theorem not_walkKeep_map_embed_some_none {M : CombMap.{u}} (a b : M.Dart) (c : List M.Dart) :
    ¬ walkKeep (toCombMap M a b) (c.map (embed M)) (some none) := by
  change ¬ (some none ∈ c.map (embed M) ∨ none ∈ c.map (embed M))
  simp [embed]

/-- **A first turn lifts across an edge insertion at distinct corners.** -/
theorem firstTurn_embed {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b) {c : List M.Dart}
    {x y : M.Dart} (h : FirstTurn M c x y) :
    FirstTurn (toCombMap M a b) (c.map (embed M)) (embed M x) (embed M y) := by
  obtain ⟨k, hk0, hky, hkeep⟩ := h
  obtain ⟨k', hkk', -, heq, hmid⟩ := exists_sigma_pow_lift hab (M.alpha x) k
  refine ⟨k', lt_of_lt_of_le hk0 hkk', ?_, fun t' ht'0 ht'k' => ?_⟩
  · change ((toCombMap M a b).sigma ^ k') (embed M (M.alpha x)) = embed M y
    rw [heq, hky]
  · change ¬ walkKeep (toCombMap M a b) (c.map (embed M))
      (((toCombMap M a b).sigma ^ t') (embed M (M.alpha x)))
    rcases hmid t' ht'0 ht'k' with ⟨t, ht0, htk, h⟩ | h | h
    · rw [h, walkKeep_map_embed_iff]
      exact hkeep t ht0 htk
    · rw [h]
      exact not_walkKeep_map_embed_none a b c
    · rw [h]
      exact not_walkKeep_map_embed_some_none a b c

/-- A turn of a boundary cycle, read on the complement walk, lifts to the image cycle. -/
theorem firstTurn_reverse_embed {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b)
    {cyc : List M.Dart} {d e : M.Dart}
    (h : FirstTurn M (cyc.reverse.map M.alpha) (M.alpha e) (M.alpha d)) :
    FirstTurn (toCombMap M a b) ((cyc.map (embed M)).reverse.map (toCombMap M a b).alpha)
      ((toCombMap M a b).alpha (embed M e)) ((toCombMap M a b).alpha (embed M d)) := by
  have h1 : FirstTurn M cyc (M.alpha e) (M.alpha d) :=
    FirstTurn.mono (fun z hz => by rwa [FirstTurnWalk.walkKeep_reverse_map_alpha]) h
  exact FirstTurn.mono
    (fun z hz => (congrFun (FirstTurnWalk.walkKeep_reverse_map_alpha
      (M := toCombMap M a b) (cyc.map (embed M))) z).mp hz)
    (firstTurn_embed hab h1)

/-- **The first-turn chain of a boundary cycle lifts** across an edge insertion at distinct
corners. -/
theorem firstTurnChain_map_embed {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b)
    {cyc : List M.Dart} (hne : cyc ≠ []) (hne' : cyc.map (embed M) ≠ [])
    (h : cyc.IsChain (fun d e => FirstTurn M (cyc.reverse.map M.alpha) (M.alpha e) (M.alpha d)) ∧
      FirstTurn M (cyc.reverse.map M.alpha) (M.alpha (cyc.head hne)) (M.alpha (cyc.getLast hne))) :
    (cyc.map (embed M)).IsChain (fun d e => FirstTurn (toCombMap M a b)
        ((cyc.map (embed M)).reverse.map (toCombMap M a b).alpha)
        ((toCombMap M a b).alpha e) ((toCombMap M a b).alpha d)) ∧
      FirstTurn (toCombMap M a b) ((cyc.map (embed M)).reverse.map (toCombMap M a b).alpha)
        ((toCombMap M a b).alpha ((cyc.map (embed M)).head hne'))
        ((toCombMap M a b).alpha ((cyc.map (embed M)).getLast hne')) := by
  refine ⟨(List.isChain_map (embed M)).mpr
    (h.1.imp fun d e hde => firstTurn_reverse_embed hab hde), ?_⟩
  rw [List.head_map, List.getLast_map]
  exact firstTurn_reverse_embed hab h.2

end EdgeInsertion

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The doubling outside the face set keeps first-turn order.** -/
theorem faceEdgeDoubling_firstTurnChain (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face)
    (j : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
    (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
    (hsrc : FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts)
    (hK : K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
          (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
          (X.toCombMap.alpha d)) ∧
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))) :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle.IsChain (fun d e =>
        FirstTurn (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
          ((K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle.reverse.map
            (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha)
          ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha e)
          ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha d)) ∧
      FirstTurn (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
        ((K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle.reverse.map
          (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha)
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle.head
            (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle_nonempty))
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle.getLast
            (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle_nonempty)) :=
  EdgeInsertion.firstTurnChain_map_embed
    (EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X f j)
      (FaceEdgeDoubling.second X f j hlen) Nat.one_pos)
    K.boundary.cycle_nonempty (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle_nonempty hK

/-- **The doubling inside the face set keeps first-turn order.** -/
theorem faceEdgeDoublingInside_firstTurnChain (K : PocketFaceSet D eps X lo hi)
    (f : X.toCombMap.Face) (j : Fin (X.faceBoundary f).darts.length)
    (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace) (hs : f ∈ K.faces)
    (hK : K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
          (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
          (X.toCombMap.alpha d)) ∧
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))) :
    (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.IsChain (fun d e =>
        FirstTurn (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
          ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.reverse.map
            (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha)
          ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha e)
          ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha d)) ∧
      FirstTurn (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
        ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.reverse.map
          (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha)
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.head
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty))
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.getLast
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty)) :=
  EdgeInsertion.firstTurnChain_map_embed
    (EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X f j)
      (FaceEdgeDoubling.second X f j hlen) Nat.one_pos)
    K.boundary.cycle_nonempty (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty hK

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.sigma_embed_apply
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.exists_sigma_pow_lift
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.firstTurn_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.firstTurnChain_map_embed
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoubling_firstTurnChain
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoublingInside_firstTurnChain
