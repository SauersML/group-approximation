import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCorners
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner options of an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The split at an uncrossed non-first turn `d₀ → e₀`
(`PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`) needs its two corners on G-faces, off the
exterior and off the relator faces.  The corner after a dart `u` at the vertex lies on the face of
`alpha u`; the x-corner has `u = e₀`, the y-corner has `u = y₀` with `σ y₀ = alpha d₀`.  A corner is
turned into a G-digon by doubling an edge of its face
(`PocketFaceSet.faceEdgeDoubling`, which needs the doubled dart off the source arc) or by thickening
an edge of the exterior (`PocketFaceSet.outerSpurThickening`, which needs the reversal of the doubled
dart off the target arc).  There are two options: double `alpha u`, keeping `u` as the corner dart, or
double `σ u`, taking the new dart before `σ u` as the corner dart.

Both options fail only when two darts consecutive in the carrier of a proper arc are both in the arc:
`alpha u` and `σ u = facePerm (alpha u)` on the source arc, or `alpha (σ u)` and `u` on the target
arc.  Then they are consecutive in the arc, so `alpha (σ u)` is followed by `u` in the boundary cycle
(`PocketFaceSet.cycle_next_of_sourceArc`, `cycle_next_of_targetArc`).  At both corners this forces
`σ e₀ = alpha d₀`, a first turn.

* `OuterPinchCornerFix.next_eq_of_infix`, `infix_of_getElem`, `infix_of_next_of_mem`: successors,
  infixes and proper cyclic arcs.
* `OuterPinchCornerFix.next_faceBoundary_darts`, `next_reverse_map_alpha`: the carriers.
* `PocketFaceSet.not_sourceArc_options_e₀`, `not_targetArc_options_e₀`, `not_sourceArc_options_y₀`,
  `not_targetArc_options_y₀`: at a non-first turn one option is available at each corner.
* `PocketFaceSet.faceOf_alpha_e₀_not_mem`, `faceOf_alpha_y₀_not_mem`: both corners lie off the face
  set.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

namespace OuterPinchCornerFix

open OuterPinchIsolated

section List

variable {α : Type*}

/-- **The entries of a two-entry infix are successors.** -/
theorem next_eq_of_infix {l : List α} (hnodup : l.Nodup) {a b : α} (h : [a, b] <:+: l)
    (ha : a ∈ l) : l.next a ha = b := by
  obtain ⟨s, t, rfl⟩ := h
  have hrot : List.IsRotated (s ++ [a, b] ++ t) (a :: b :: (t ++ s)) :=
    ⟨s.length, by rw [List.append_assoc]; exact List.rotate_append_length_eq s (a :: b :: t)⟩
  rw [List.isRotated_next_eq hrot hnodup ha, List.next_cons_cons_eq]

/-- **Two adjacent entries form an infix.** -/
theorem infix_of_getElem {l : List α} {i : ℕ} (hi : i + 1 < l.length) :
    [l[i], l[i + 1]] <:+: l := by
  have h1 : l.drop i = l[i] :: l[i + 1] :: l.drop (i + 1 + 1) := by
    rw [List.drop_eq_getElem_cons (i := i) (l := l) (by omega),
      List.drop_eq_getElem_cons (i := i + 1) (l := l) hi]
  have h2 : (l.drop i).take 2 = [l[i], l[i + 1]] := by
    rw [h1]
    rfl
  rw [← h2]
  exact (List.take_prefix 2 (l.drop i)).isInfix.trans (List.drop_suffix i l).isInfix

/-- **Successors of the carrier inside a proper arc.**  Two darts that are successors in the
carrier and both lie in a proper cyclic arc are adjacent in the arc. -/
theorem infix_of_next_of_mem {l : List α} (arc : CyclicArc l) (hnodup : l.Nodup)
    (hprop : arc.length < l.length) {a b : α} (ha : a ∈ arc.darts) (hb : b ∈ arc.darts)
    (hab : l.next a (arc.mem_cycle_of_mem_darts ha) = b) : [a, b] <:+: arc.darts := by
  obtain ⟨r, hr⟩ : ∃ r, l.rotate arc.start.1 = r := ⟨_, rfl⟩
  have hrot : List.IsRotated l r := ⟨arc.start.1, hr⟩
  have hdarts : arc.darts = r.take arc.length := by
    rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate, hr]
  have hnr : r.Nodup := by
    rw [← hr]
    exact List.nodup_rotate.mpr hnodup
  have hlen : r.length = l.length := by
    rw [← hr, List.length_rotate]
  have ha' : a ∈ r.take arc.length := by
    rw [← hdarts]
    exact ha
  have hb' : b ∈ r.take arc.length := by
    rw [← hdarts]
    exact hb
  obtain ⟨i, hi, hia⟩ := List.mem_take_iff_getElem.mp ha'
  obtain ⟨j, hj, hjb⟩ := List.mem_take_iff_getElem.mp hb'
  have hab' : r.next a (hrot.mem_iff.mp (arc.mem_cycle_of_mem_darts ha)) = b :=
    (List.isRotated_next_eq hrot hnodup (arc.mem_cycle_of_mem_darts ha)).symm.trans hab
  have hi' : i < r.length := by omega
  subst hia
  rw [List.next_getElem r hnr i hi'] at hab'
  have hmod : (i + 1) % r.length = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hji : j = i + 1 := by
    have h := hjb.trans hab'.symm
    rw [List.Nodup.getElem_inj_iff hnr] at h
    rw [hmod] at h
    exact h
  subst hjb
  subst hji
  rw [hdarts]
  have hinf := infix_of_getElem (l := r.take arc.length) (i := i)
    (by rw [List.length_take]; omega)
  simp only [List.getElem_take] at hinf
  exact hinf

/-- **Successors through an injective map.** -/
theorem next_map_of_injective {β : Type*} {f : α → β} (hf : Function.Injective f) {l : List α}
    (hl : l.Nodup) {a : α} (ha : a ∈ l) (hb : f a ∈ l.map f) :
    (l.map f).next (f a) hb = f (l.next a ha) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (l.map f).length := by
    rw [List.length_map]
    exact hi
  have h := List.next_getElem (l.map f) (List.Nodup.map hf hl) i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [h, List.next_getElem l hl i hi]

end List

section Carrier

variable {M : CombMap.{u}}

/-- **The successor in a face traversal is the face permutation.** -/
theorem next_faceBoundary_darts {f : M.Face} (B : FaceBoundary M f) {d : M.Dart}
    (hd : d ∈ B.darts) : B.darts.next d hd = M.facePerm d :=
  (rel_next_of_isChain B.nonempty B.nodup B.chain B.closes hd).symm

/-- The face permutation after a reversal is the rotation. -/
theorem facePerm_alpha (d : M.Dart) : M.facePerm (M.alpha d) = M.sigma d := by
  unfold CombMap.facePerm
  rw [Equiv.Perm.mul_apply, M.alpha_involutive]

/-- **The successor on a reversed face traversal.**  On the traversal read backwards and reversed,
the dart `alpha (σ u)` is followed by `u`. -/
theorem next_reverse_map_alpha {f : M.Face} (B : FaceBoundary M f) {u : M.Dart}
    (hu : M.alpha u ∈ B.darts) (h : M.alpha (M.sigma u) ∈ B.darts.reverse.map M.alpha) :
    (B.darts.reverse.map M.alpha).next (M.alpha (M.sigma u)) h = u := by
  have hnext : B.darts.next (M.alpha u) hu = M.sigma u := by
    rw [next_faceBoundary_darts B hu, facePerm_alpha]
  have hmem : M.sigma u ∈ B.darts := by
    rw [← hnext]
    exact List.next_mem ..
  have hcongr : ∀ (a b : M.Dart) (ha : a ∈ B.darts) (hb : b ∈ B.darts), a = b →
      B.darts.prev a ha = B.darts.prev b hb := by
    rintro a b ha hb rfl
    rfl
  have hprev : B.darts.prev (M.sigma u) hmem = M.alpha u :=
    (hcongr _ _ hmem (List.next_mem ..) hnext.symm).trans (List.prev_next B.darts B.nodup _ hu)
  rw [next_map_of_injective M.alpha.injective (List.nodup_reverse.mpr B.nodup)
    (List.mem_reverse.mpr hmem) h, List.next_reverse_eq_prev B.darts B.nodup _ hmem, hprev,
    M.alpha_involutive]

/-- **A cycle successor forcing the x-corner turn.**  If `alpha (σ e₀)` is followed by `e₀`, as `d₀`
is, then `σ e₀ = alpha d₀`. -/
theorem sigma_eq_of_cycle_next_e₀ {c : List M.Dart} (hnodup : c.Nodup) {d₀ e₀ : M.Dart}
    (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀)
    (h : ∃ h : M.alpha (M.sigma e₀) ∈ c, c.next _ h = e₀) : M.sigma e₀ = M.alpha d₀ := by
  obtain ⟨h, hn⟩ := h
  have hprev : ∀ (a b : M.Dart) (ha : a ∈ c) (hb : b ∈ c), a = b → c.prev a ha = c.prev b hb := by
    rintro a b ha hb rfl
    rfl
  have hd : M.alpha (M.sigma e₀) = d₀ :=
    ((List.prev_next c hnodup _ h).symm.trans (hprev _ _ _ _ (hn.trans hnext₀.symm))).trans
      (List.prev_next c hnodup d₀ hd₀)
  rw [← hd, M.alpha_involutive]

/-- **A cycle successor forcing the y-corner turn.**  If `alpha (σ y₀) = d₀` is followed by `y₀`,
then `y₀ = e₀` and `σ e₀ = alpha d₀`. -/
theorem sigma_eq_of_cycle_next_y₀ {c : List M.Dart} {d₀ e₀ y₀ : M.Dart} (hd₀ : d₀ ∈ c)
    (hnext₀ : c.next d₀ hd₀ = e₀) (hy₀ : M.sigma y₀ = M.alpha d₀)
    (h : ∃ h : M.alpha (M.sigma y₀) ∈ c, c.next _ h = y₀) : M.sigma e₀ = M.alpha d₀ := by
  obtain ⟨h, hn⟩ := h
  have hcongr : ∀ (a b : M.Dart) (ha : a ∈ c) (hb : b ∈ c), a = b → c.next a ha = c.next b hb := by
    rintro a b ha hb rfl
    rfl
  have hd : M.alpha (M.sigma y₀) = d₀ := by
    rw [hy₀, M.alpha_involutive]
  have he : e₀ = y₀ := hnext₀.symm.trans ((hcongr _ _ hd₀ h hd.symm).trans hn)
  rw [he, hy₀]

/-- **One rotation step to `alpha d₀` is a first turn.** -/
theorem firstTurn_of_sigma_eq {c : List M.Dart} {d₀ e₀ : M.Dart}
    (h : M.sigma e₀ = M.alpha d₀) :
    FirstTurn M (c.reverse.map M.alpha) (M.alpha e₀) (M.alpha d₀) :=
  FirstTurn.reverse_map_alpha_iff.mpr
    ⟨1, Nat.one_pos, by rw [pow_one]; exact h, fun _ ht0 ht1 => absurd ht1 (by omega)⟩

end Carrier

end OuterPinchCornerFix

open OuterPinchCornerFix

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The source arc, read backwards and reversed, is an infix of the boundary cycle. -/
theorem invDarts_sourceArc_infix (K : PocketFaceSet D eps X lo hi) :
    invDarts X K.sourceArc.darts <:+: K.boundary.cycle := by
  rw [K.decomposition]
  exact (List.infix_append K.firstSide _ K.secondSide).trans (List.prefix_append _ _).isInfix

/-- The target arc is an infix of the boundary cycle. -/
theorem targetArc_infix (K : PocketFaceSet D eps X lo hi) :
    K.targetArc.darts <:+: K.boundary.cycle := by
  rw [K.decomposition]
  exact (List.suffix_append _ _).isInfix

/-- **Both options on the source arc.**  If `alpha u` and `σ u` both lie in a proper source arc, then
`alpha (σ u)` is followed by `u` in the boundary cycle. -/
theorem cycle_next_of_sourceArc (K : PocketFaceSet D eps X lo hi)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length) {u : X.toCombMap.Dart}
    (ha : X.toCombMap.alpha u ∈ K.sourceArc.darts) (hb : X.toCombMap.sigma u ∈ K.sourceArc.darts) :
    ∃ h : X.toCombMap.alpha (X.toCombMap.sigma u) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = u := by
  have hcarrier : (cellDarts X K.source).next (X.toCombMap.alpha u)
      (K.sourceArc.mem_cycle_of_mem_darts ha) = X.toCombMap.sigma u :=
    (next_faceBoundary_darts (X.faceBoundary (cell X K.source).face)
      (K.sourceArc.mem_cycle_of_mem_darts ha)).trans (facePerm_alpha u)
  have hinf := infix_of_next_of_mem K.sourceArc (X.faceBoundary (cell X K.source).face).nodup hprop
    ha hb hcarrier
  have hinf2 := (List.IsInfix.map X.toCombMap.alpha hinf.reverse).trans K.invDarts_sourceArc_infix
  have e : [X.toCombMap.alpha u, X.toCombMap.sigma u].reverse.map X.toCombMap.alpha =
      [X.toCombMap.alpha (X.toCombMap.sigma u), u] := by
    simp [X.toCombMap.alpha_involutive u]
  rw [e] at hinf2
  exact ⟨hinf2.mem (by simp), next_eq_of_infix K.boundary.cycle_nodup hinf2 _⟩

/-- **Both options on the target arc.**  If `u` and `alpha (σ u)` both lie in a proper target arc,
then `alpha (σ u)` is followed by `u` in the boundary cycle. -/
theorem cycle_next_of_targetArc (K : PocketFaceSet D eps X lo hi)
    (htgt : K.targetArc.length < (outerDarts X).length) {u : X.toCombMap.Dart}
    (ha : u ∈ K.targetArc.darts) (hb : X.toCombMap.alpha (X.toCombMap.sigma u) ∈ K.targetArc.darts) :
    ∃ h : X.toCombMap.alpha (X.toCombMap.sigma u) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = u := by
  have hnodup : (outerDarts X).Nodup :=
    (List.nodup_reverse.mpr (X.faceBoundary X.outerFace).nodup).map X.toCombMap.alpha.injective
  have hu : X.toCombMap.alpha u ∈ (X.faceBoundary X.outerFace).darts := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (K.targetArc.mem_cycle_of_mem_darts ha)
    rw [X.toCombMap.alpha_involutive]
    exact List.mem_reverse.mp hd
  have hcarrier : (outerDarts X).next _ (K.targetArc.mem_cycle_of_mem_darts hb) = u :=
    next_reverse_map_alpha (X.faceBoundary X.outerFace) hu _
  have hinf2 := (infix_of_next_of_mem K.targetArc hnodup htgt hb ha hcarrier).trans K.targetArc_infix
  exact ⟨hinf2.mem (by simp), next_eq_of_infix K.boundary.cycle_nodup hinf2 _⟩

section Options

variable (K : PocketFaceSet D eps X lo hi) {d₀ e₀ : X.toCombMap.Dart}
  (hd₀ : d₀ ∈ K.boundary.cycle) (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
  (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
    (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
include hd₀ hnext₀ hnot

/-- **An option at the x-corner off the source arc.** -/
theorem not_sourceArc_options_e₀ (hprop : K.sourceArc.length < (cellDarts X K.source).length) :
    ¬ (X.toCombMap.alpha e₀ ∈ K.sourceArc.darts ∧ X.toCombMap.sigma e₀ ∈ K.sourceArc.darts) :=
  fun h => hnot (firstTurn_of_sigma_eq (sigma_eq_of_cycle_next_e₀ K.boundary.cycle_nodup hd₀ hnext₀
    (K.cycle_next_of_sourceArc hprop h.1 h.2)))

/-- **An option at the x-corner off the target arc.** -/
theorem not_targetArc_options_e₀ (htgt : K.targetArc.length < (outerDarts X).length) :
    ¬ (e₀ ∈ K.targetArc.darts ∧
      X.toCombMap.alpha (X.toCombMap.sigma e₀) ∈ K.targetArc.darts) :=
  fun h => hnot (firstTurn_of_sigma_eq (sigma_eq_of_cycle_next_e₀ K.boundary.cycle_nodup hd₀ hnext₀
    (K.cycle_next_of_targetArc htgt h.1 h.2)))

/-- **An option at the y-corner off the source arc.** -/
theorem not_sourceArc_options_y₀ (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    {y₀ : X.toCombMap.Dart} (hy₀ : X.toCombMap.sigma y₀ = X.toCombMap.alpha d₀) :
    ¬ (X.toCombMap.alpha y₀ ∈ K.sourceArc.darts ∧ X.toCombMap.sigma y₀ ∈ K.sourceArc.darts) :=
  fun h => hnot (firstTurn_of_sigma_eq (sigma_eq_of_cycle_next_y₀ hd₀ hnext₀ hy₀
    (K.cycle_next_of_sourceArc hprop h.1 h.2)))

/-- **An option at the y-corner off the target arc.** -/
theorem not_targetArc_options_y₀ (htgt : K.targetArc.length < (outerDarts X).length)
    {y₀ : X.toCombMap.Dart} (hy₀ : X.toCombMap.sigma y₀ = X.toCombMap.alpha d₀) :
    ¬ (y₀ ∈ K.targetArc.darts ∧
      X.toCombMap.alpha (X.toCombMap.sigma y₀) ∈ K.targetArc.darts) :=
  fun h => hnot (firstTurn_of_sigma_eq (sigma_eq_of_cycle_next_y₀ hd₀ hnext₀ hy₀
    (K.cycle_next_of_targetArc htgt h.1 h.2)))

end Options

/-- **The x-corner lies off the face set.** -/
theorem faceOf_alpha_e₀_not_mem (K : PocketFaceSet D eps X lo hi) {e₀ : X.toCombMap.Dart}
    (he₀ : e₀ ∈ K.boundary.cycle) : X.toCombMap.faceOf (X.toCombMap.alpha e₀) ∉ K.faces :=
  ((K.boundary.cycle_mem_iff e₀).mp he₀).2

/-- **The y-corner lies off the face set.** -/
theorem faceOf_alpha_y₀_not_mem (K : PocketFaceSet D eps X lo hi) {d₀ y₀ : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) (hy₀ : X.toCombMap.sigma y₀ = X.toCombMap.alpha d₀) :
    X.toCombMap.faceOf (X.toCombMap.alpha y₀) ∉ K.faces := by
  rw [← X.toCombMap.faceOf_facePerm, facePerm_alpha, hy₀]
  exact ((K.boundary.cycle_mem_iff d₀).mp hd₀).2

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.next_eq_of_infix
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.infix_of_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.infix_of_next_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.next_map_of_injective
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.next_faceBoundary_darts
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.facePerm_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.next_reverse_map_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.sigma_eq_of_cycle_next_e₀
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.sigma_eq_of_cycle_next_y₀
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerFix.firstTurn_of_sigma_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.invDarts_sourceArc_infix
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.targetArc_infix
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.cycle_next_of_sourceArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.cycle_next_of_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.not_sourceArc_options_e₀
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.not_targetArc_options_e₀
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.not_sourceArc_options_y₀
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.not_targetArc_options_y₀
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_e₀_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_y₀_not_mem
