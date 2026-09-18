import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting the lake-filled outer walk of a cell pocket walk along its two arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `K = s₁ t₁⁻¹ s₂ t₂⁻¹` be a cell pocket walk (`CellPocketWalk`) which is a noncrossing closed
walk, and let both cells `Π_i`, `Π_j` lie in the piece of the exterior face off the side faces of
`K`.  Filling the lakes gives the outer walk `lakeWalk` started at a walk-edge dart `x₀` facing
the exterior piece.  Its reversal `invDarts X (lakeWalk …)` consists of the darts `d` of `K` whose
reversal `α d` faces the exterior piece (`LakeFill.mem_lakeWalk_iff`).

This file reduces the order statement `exists_lakeWalk_bothExterior` (work order WO-GL03BPinch-1)
to one sublist property of the outer walk.

* `exists_eq_append_of_sublist`: a sublist of a duplicate-free concatenation `a ++ b ++ c ++ d`
  containing every element of `b` and of `d` is `s₁ ++ b ++ s₂ ++ d` with `s₁ <+ a`, `s₂ <+ c`.
* `arc_lake_mem_first`, `arc_lake_mem_second`: the reversal of every arc dart is a dart of the
  walk, and the arc dart faces the cell, hence the exterior piece.
* `exists_lakeWalk_eq_of_sublist`: if the reversed outer walk is a sublist of `K`, it is
  `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂⁻¹` with `s₁ <+ firstSide` and `s₂ <+ secondSide`.
* `exists_lakeWalk_bothExterior_of_exists_sublist`: the conclusion of
  `exists_lakeWalk_bothExterior`, with `s₁.length ≤ ε` and `s₂.length ≤ ε` separately, from the
  existence of a start dart whose reversed outer walk is a sublist of `K`.
* `secondArcDart`, `walk_eq_append_alpha_secondArcDart`, `faceOf_secondArcDart_mem`: the natural
  start dart, the first dart of the second arc, whose reversal is the last dart of `K`.
* `exists_lakeWalk_bothExterior_of_sublist`: the conclusion of `exists_lakeWalk_bothExterior` from
  the sublist property at `secondArcDart K`.

The remaining input is the order lemma: under the inner Euler equality, the reversed outer walk
started at a dart whose reversal is the last dart of the walk is a sublist of the walk.  The Euler
hypothesis is needed for this route: `IsNoncrossingClosedWalk` only forbids crossings at single
vertices, and when the inner reclosing is not a sphere the outer walk need not follow the walk in
order.
-/

namespace GroupApproximation.Full.GL03BPinchOrder

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
  GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill
  GroupApproximation.GGT.VanKampen.Embedded

/-- **A sublist of four blocks keeping two whole blocks.**  If `l` is a sublist of the
duplicate-free list `a ++ b ++ c ++ d` and contains every element of `b` and of `d`, then
`l = s₁ ++ b ++ s₂ ++ d` with `s₁ <+ a` and `s₂ <+ c`.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem exists_eq_append_of_sublist {α : Type*} {l a b c d : List α}
    (hl : l <+ a ++ b ++ c ++ d) (hnd : (a ++ b ++ c ++ d).Nodup)
    (hb : ∀ x ∈ b, x ∈ l) (hd : ∀ x ∈ d, x ∈ l) :
    ∃ s₁ s₂ : List α, l = s₁ ++ b ++ s₂ ++ d ∧ s₁ <+ a ∧ s₂ <+ c := by
  obtain ⟨l₁, l₄, rfl, hl₁, hl₄⟩ := List.sublist_append_iff.mp hl
  obtain ⟨l₂, l₃, rfl, hl₂, hl₃⟩ := List.sublist_append_iff.mp hl₁
  obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ := List.sublist_append_iff.mp hl₂
  obtain ⟨habc, hdnd, hdisj⟩ := List.nodup_append.mp hnd
  obtain ⟨hab, -, hdisj₂⟩ := List.nodup_append.mp habc
  obtain ⟨-, hbnd, hdisj₁⟩ := List.nodup_append.mp hab
  have hbsub : b ⊆ m₂ := by
    intro x hx
    have hxl := hb x hx
    rcases List.mem_append.mp hxl with hxl | hx₄
    · rcases List.mem_append.mp hxl with hxl | hx₃
      · rcases List.mem_append.mp hxl with hx₁ | hx₂
        · exact (hdisj₁ x (hm₁.subset hx₁) x hx rfl).elim
        · exact hx₂
      · exact (hdisj₂ x (List.mem_append_right a hx) x (hl₃.subset hx₃) rfl).elim
    · exact (hdisj x (List.mem_append_left c (List.mem_append_right a hx)) x
        (hl₄.subset hx₄) rfl).elim
  have hdsub : d ⊆ l₄ := by
    intro x hx
    have hxl := hd x hx
    rcases List.mem_append.mp hxl with hxl | hx₄
    · rcases List.mem_append.mp hxl with hxl | hx₃
      · rcases List.mem_append.mp hxl with hx₁ | hx₂
        · exact (hdisj x (List.mem_append_left c (List.mem_append_left b (hm₁.subset hx₁))) x
            hx rfl).elim
        · exact (hdisj x (List.mem_append_left c (List.mem_append_right a (hm₂.subset hx₂))) x
            hx rfl).elim
      · exact (hdisj x (List.mem_append_right (a ++ b) (hl₃.subset hx₃)) x hx rfl).elim
    · exact hx₄
  have hm₂eq : m₂ = b :=
    hm₂.eq_of_length_le (List.subperm_of_subset hbnd hbsub).length_le
  have hl₄eq : l₄ = d :=
    hl₄.eq_of_length_le (List.subperm_of_subset hdnd hdsub).length_le
  subst hm₂eq
  subst hl₄eq
  exact ⟨m₁, l₃, rfl, hm₁, hl₃⟩

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Reversed darts of the outer walk.**  If every dart `e` of `t` has its reversal on the walk
`K` and faces the exterior piece, then every dart of `invDarts X t` is a dart of the reversed outer
walk `invDarts X (lakeWalk …)`.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem mem_invDarts_lakeWalk_of_forall (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    {x₀ : (walkMap X.toCombMap K.walk).Dart}
    (hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {t : List X.toCombMap.Dart}
    (ht : ∀ e ∈ t, X.toCombMap.alpha e ∈ K.walk ∧
      X.toCombMap.faceOf e ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∀ x ∈ invDarts X t, x ∈ invDarts X (lakeWalk X.toCombMap K.walk x₀) := by
  intro x hx
  simp only [invDarts] at hx ⊢
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr
    ((mem_lakeWalk_iff hw X.planar hout hx₀ e).mpr (ht e (List.mem_reverse.mp he))))

/-- **The first arc lies on the outer walk.**  The reversal of a dart of the first arc `t₁` is a
dart of `K`, and the dart faces `Π_i`, which lies in the exterior piece.  (Osin, proof of
Lemma 9.7(b); `thm:hull`.) -/
theorem arc_lake_mem_first (K : CellPocketWalk D eps X i j)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∀ e ∈ K.firstArc.darts, X.toCombMap.alpha e ∈ K.walk ∧
      X.toCombMap.faceOf e ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace := by
  intro e he
  refine ⟨?_, ?_⟩
  · have h : X.toCombMap.alpha e ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
        invDarts X K.secondArc.darts :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr he))))
    exact h
  · rw [((X.faceBoundary (cell X i).face).mem_iff e).mp (K.firstArc.mem_cycle_of_mem_darts he)]
    exact hi

/-- The reversal of a dart of the second arc `t₂` is a dart of the pocket walk `K`. -/
theorem alpha_mem_walk_of_mem_secondArc (K : CellPocketWalk D eps X i j)
    {e : X.toCombMap.Dart} (he : e ∈ K.secondArc.darts) : X.toCombMap.alpha e ∈ K.walk := by
  have h : X.toCombMap.alpha e ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
      invDarts X K.secondArc.darts :=
    List.mem_append_right _
      (List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr he))
  exact h

/-- **The second arc lies on the outer walk.**  The reversal of a dart of the second arc `t₂` is a
dart of `K`, and the dart faces `Π_j`, which lies in the exterior piece.  (Osin, proof of
Lemma 9.7(b); `thm:hull`.) -/
theorem arc_lake_mem_second (K : CellPocketWalk D eps X i j)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∀ e ∈ K.secondArc.darts, X.toCombMap.alpha e ∈ K.walk ∧
      X.toCombMap.faceOf e ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace := by
  intro e he
  refine ⟨alpha_mem_walk_of_mem_secondArc K he, ?_⟩
  rw [((X.faceBoundary (cell X j).face).mem_iff e).mp (K.secondArc.mem_cycle_of_mem_darts he)]
  exact hj

/-- **The split of the outer walk.**  If the reversed outer walk of a start dart facing the
exterior piece is a sublist of the pocket walk `K = s₁ ++ t₁⁻¹ ++ s₂ ++ t₂⁻¹`, then it is
`s₁' ++ t₁⁻¹ ++ s₂' ++ t₂⁻¹` with `s₁' <+ s₁` and `s₂' <+ s₂`.  (Osin, proof of Lemma 9.7(b);
`thm:hull`.) -/
theorem exists_lakeWalk_eq_of_sublist (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (x₀ : (walkMap X.toCombMap K.walk).Dart)
    (hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hsub : invDarts X (lakeWalk X.toCombMap K.walk x₀) <+ K.walk) :
    ∃ s₁ s₂ : List X.toCombMap.Dart,
      invDarts X (lakeWalk X.toCombMap K.walk x₀) =
          s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts ∧
        s₁ <+ K.firstSide ∧ s₂ <+ K.secondSide :=
  exists_eq_append_of_sublist (a := K.firstSide) (b := invDarts X K.firstArc.darts)
    (c := K.secondSide) (d := invDarts X K.secondArc.darts) hsub hw.nodup
    (mem_invDarts_lakeWalk_of_forall K hw hout hx₀ (arc_lake_mem_first K hi))
    (mem_invDarts_lakeWalk_of_forall K hw hout hx₀ (arc_lake_mem_second K hj))

/-- **The order statement from a sublist start dart.**  The conclusion of
`exists_lakeWalk_bothExterior` (work order WO-GL03BPinch-1), with the two side pieces bounded by
`ε` separately, from a start dart facing the exterior piece whose reversed outer walk is a sublist
of the pocket walk.  (Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex 2134.) -/
theorem exists_lakeWalk_bothExterior_of_exists_sublist (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (h : ∃ x₀ : (walkMap X.toCombMap K.walk).Dart,
      X.toCombMap.faceOf x₀.1 ∈
          component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace ∧
        invDarts X (lakeWalk X.toCombMap K.walk x₀) <+ K.walk) :
    ∃ (x₀ : (walkMap X.toCombMap K.walk).Dart) (s₁ s₂ : List X.toCombMap.Dart),
      X.toCombMap.faceOf x₀.1 ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace ∧
      invDarts X (lakeWalk X.toCombMap K.walk x₀) =
        s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps := by
  obtain ⟨x₀, hx₀, hsub⟩ := h
  obtain ⟨s₁, s₂, heq, hs₁, hs₂⟩ := exists_lakeWalk_eq_of_sublist K hw hout hi hj x₀ hx₀ hsub
  exact ⟨x₀, s₁, s₂, hx₀, heq, hs₁.length_le.trans K.firstSide_length_le,
    hs₂.length_le.trans K.secondSide_length_le⟩

/-- The second arc of a cell pocket walk is nonempty. -/
theorem secondArc_darts_ne_nil (K : CellPocketWalk D eps X i j) : K.secondArc.darts ≠ [] :=
  List.ne_nil_of_length_pos (by rw [K.secondArc.darts_length]; exact K.secondArc_pos)

/-- **The pocket walk ends with the reversal of the first dart of the second arc.**
`K = s₁ ++ t₁⁻¹ ++ s₂ ++ (tail t₂)⁻¹ ++ [α (head t₂)]`.  (Osin, proof of Lemma 9.7(b);
`thm:hull`.) -/
theorem walk_eq_append_alpha_head (K : CellPocketWalk D eps X i j) :
    K.walk = (K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
        invDarts X K.secondArc.darts.tail) ++
      [X.toCombMap.alpha (K.secondArc.darts.head (secondArc_darts_ne_nil K))] := by
  have h := List.cons_head_tail (secondArc_darts_ne_nil K)
  have hw : K.walk = K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
      invDarts X (K.secondArc.darts.head (secondArc_darts_ne_nil K) :: K.secondArc.darts.tail) := by
    rw [h]
    rfl
  rw [hw]
  simp only [invDarts, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc]

/-- **The natural start dart**: the first dart of the second arc `t₂`, a dart of the walk map since
its reversal is the last dart of `K`.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
noncomputable def secondArcDart (K : CellPocketWalk D eps X i j) :
    (walkMap X.toCombMap K.walk).Dart :=
  ⟨K.secondArc.darts.head (secondArc_darts_ne_nil K), Or.inr
    (alpha_mem_walk_of_mem_secondArc K (List.head_mem (secondArc_darts_ne_nil K)))⟩

/-- The start dart `secondArcDart K` is the first dart of the second arc. -/
theorem secondArcDart_val (K : CellPocketWalk D eps X i j) :
    (secondArcDart K).1 = K.secondArc.darts.head (secondArc_darts_ne_nil K) :=
  rfl

/-- **The reversal of the start dart is the last dart of `K`.**  (Osin, proof of Lemma 9.7(b);
`thm:hull`.) -/
theorem walk_eq_append_alpha_secondArcDart (K : CellPocketWalk D eps X i j) :
    ∃ s : List X.toCombMap.Dart, K.walk = s ++ [X.toCombMap.alpha (secondArcDart K).1] :=
  ⟨_, walk_eq_append_alpha_head K⟩

/-- **The start dart faces the exterior piece**: it is a dart of `Π_j`.  (Osin, proof of
Lemma 9.7(b); `thm:hull`.) -/
theorem faceOf_secondArcDart_mem (K : CellPocketWalk D eps X i j)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    X.toCombMap.faceOf (secondArcDart K).1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace :=
  (arc_lake_mem_second K hj _ (List.head_mem (secondArc_darts_ne_nil K))).2

/-- **The order statement from the sublist property at the natural start dart.**  If the reversed
outer walk started at the first dart of the second arc is a sublist of the pocket walk, the
conclusion of `exists_lakeWalk_bothExterior` holds.  (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex 2134.) -/
theorem exists_lakeWalk_bothExterior_of_sublist (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hsub : invDarts X (lakeWalk X.toCombMap K.walk (secondArcDart K)) <+ K.walk) :
    ∃ (x₀ : (walkMap X.toCombMap K.walk).Dart) (s₁ s₂ : List X.toCombMap.Dart),
      X.toCombMap.faceOf x₀.1 ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace ∧
      invDarts X (lakeWalk X.toCombMap K.walk x₀) =
        s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps :=
  exists_lakeWalk_bothExterior_of_exists_sublist K hw hout hi hj
    ⟨secondArcDart K, faceOf_secondArcDart_mem K hj, hsub⟩

end GroupApproximation.Full.GL03BPinchOrder

#audit_axioms GroupApproximation.Full.GL03BPinchOrder.exists_eq_append_of_sublist
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.mem_invDarts_lakeWalk_of_forall
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.arc_lake_mem_first
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.alpha_mem_walk_of_mem_secondArc
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.arc_lake_mem_second
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.exists_lakeWalk_eq_of_sublist
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.exists_lakeWalk_bothExterior_of_exists_sublist
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.secondArc_darts_ne_nil
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.walk_eq_append_alpha_head
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.secondArcDart_val
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.walk_eq_append_alpha_secondArcDart
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.faceOf_secondArcDart_mem
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.exists_lakeWalk_bothExterior_of_sublist
