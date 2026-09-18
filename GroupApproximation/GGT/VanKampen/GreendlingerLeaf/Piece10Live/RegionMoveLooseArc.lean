import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCoreCloseTight
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCornerFix
import GroupApproximation.Meta.AxiomGuard

/-!
# Passages inside an arc are tight

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-20.

Write `σ` for the rotation and `α` for the reversal.  A passage `d → next d` of the boundary cycle
of a pocket is *tight* (`RegionMoveCoreCloseTight`) when `σ (next d) = α d`.

## Route

* `regionMoveLoose_next_of_infix_cyclicArc`: two adjacent darts of a cyclic arc are successors in
  the carrier.
* `regionMoveLoose_tight_of_infix_targetArc`: a passage `a → b` with `[a, b]` adjacent in `t₂` is
  tight.  The successor of `a` on the outer darts is `b`, and on the outer darts
  (the reversed outer face) `σ b = α a` (`sigma_eq_of_cycle_next_e₀`).
* `regionMoveLoose_tight_of_infix_sourceArc`: a passage `a → b` with `[a, b]` adjacent in `t₁⁻¹` is
  tight.  Then `[α b, α a]` is adjacent in `t₁`, so `facePerm (α b) = α a`, that is `σ b = α a`.
* `regionMoveLoose_tight_or_junction`: every passage of the boundary cycle is tight, starts in a
  side `s₁` or `s₂`, or starts at the last dart of `t₁⁻¹` or of `t₂` (a *junction*).

## Truth check

Proved lemmas.  They only use that the pocket boundary is `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` with no repeated
dart, and that consecutive darts of a face traversal are related by the face permutation.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

/-- **Adjacent darts of a cyclic arc are successors in the carrier.** -/
theorem regionMoveLoose_next_of_infix_cyclicArc {β : Type*} {l : List β} (hl : l.Nodup)
    (arc : CyclicArc l) {a b : β} (h : [a, b] <:+: arc.darts) :
    ∃ ha : a ∈ l, l.next a ha = b := by
  have hrot : List.IsRotated l (l.rotate arc.start.1) := ⟨arc.start.1, rfl⟩
  have hd : arc.darts <:+: l.rotate arc.start.1 := by
    rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate]
    exact (List.take_prefix _ _).isInfix
  have hinf : [a, b] <:+: l.rotate arc.start.1 := h.trans hd
  have ha : a ∈ l := hrot.mem_iff.mpr (hinf.mem (by simp))
  refine ⟨ha, ?_⟩
  rw [List.isRotated_next_eq hrot hl ha]
  exact OuterPinchCornerFix.next_eq_of_infix (List.nodup_rotate.mpr hl) hinf _

/-- **Reading an infix of a reversed image back.** -/
theorem regionMoveLoose_infix_reverse_map {β : Type*} {f : β → β} (hf : Function.Involutive f)
    {l : List β} {a b : β} (h : [a, b] <:+: l.reverse.map f) : [f b, f a] <:+: l := by
  have h1 := (h.map f).reverse
  have e1 : ([a, b].map f).reverse = [f b, f a] := by simp
  have e2 : ((l.reverse.map f).map f).reverse = l := by
    rw [List.map_map, List.map_id'' (f := f ∘ f) (fun x => hf x), List.reverse_reverse]
  rw [e1, e2] at h1
  exact h1

/-- **An entry other than the last one starts a two-entry infix.** -/
theorem regionMoveLoose_exists_infix_of_ne_getLast {β : Type*} {l : List β} {e : β}
    (he : e ∈ l) (hne : ∀ h : l ≠ [], e ≠ l.getLast h) : ∃ b, [e, b] <:+: l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  by_cases hlt : i + 1 < l.length
  · exact ⟨l[i + 1], OuterPinchCornerFix.infix_of_getElem hlt⟩
  · exfalso
    apply hne (List.ne_nil_of_mem he)
    rw [List.getLast_eq_getElem]
    congr 1
    omega

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Successors on the outer darts are tight**: on the reversed outer face, if `b` follows `a`,
then `σ b = α a`. -/
theorem regionMoveLoose_sigma_eq_of_outerDarts_next {a b : X.toCombMap.Dart}
    (ha : a ∈ outerDarts X) (hab : (outerDarts X).next a ha = b) :
    X.toCombMap.sigma b = X.toCombMap.alpha a := by
  have hnodup : (outerDarts X).Nodup :=
    (List.nodup_reverse.mpr (X.faceBoundary X.outerFace).nodup).map X.toCombMap.alpha.injective
  have hb : b ∈ outerDarts X := by
    rw [← hab]
    exact List.next_mem ha
  have hu : X.toCombMap.alpha b ∈ (X.faceBoundary X.outerFace).darts := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    rw [X.toCombMap.alpha_involutive]
    exact List.mem_reverse.mp hd
  have hs : X.toCombMap.sigma b ∈ (X.faceBoundary X.outerFace).darts := by
    have h1 := List.next_mem hu
    rwa [OuterPinchCornerFix.next_faceBoundary_darts (X.faceBoundary X.outerFace) hu,
      OuterPinchCornerFix.facePerm_alpha] at h1
  have hm : X.toCombMap.alpha (X.toCombMap.sigma b) ∈ outerDarts X :=
    List.mem_map_of_mem (List.mem_reverse.mpr hs)
  exact OuterPinchCornerFix.sigma_eq_of_cycle_next_e₀ hnodup ha hab
    ⟨hm, OuterPinchCornerFix.next_reverse_map_alpha (X.faceBoundary X.outerFace) hu hm⟩

/-- **A passage inside the target arc is tight.** -/
theorem regionMoveLoose_tight_of_infix_targetArc (K : PocketFaceSet D eps X lo hi)
    {a b : X.toCombMap.Dart} (h : [a, b] <:+: K.targetArc.darts) (ha : a ∈ K.boundary.cycle) :
    RegionMoveCoreCloseTight K a ha := by
  have hnodup : (outerDarts X).Nodup :=
    (List.nodup_reverse.mpr (X.faceBoundary X.outerFace).nodup).map X.toCombMap.alpha.injective
  obtain ⟨ha', hab⟩ := regionMoveLoose_next_of_infix_cyclicArc hnodup K.targetArc h
  have hnext : K.boundary.cycle.next a ha = b :=
    OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup (h.trans K.targetArc_infix) ha
  unfold RegionMoveCoreCloseTight
  rw [hnext]
  exact regionMoveLoose_sigma_eq_of_outerDarts_next ha' hab

/-- **A passage inside the reversed source arc is tight.** -/
theorem regionMoveLoose_tight_of_infix_sourceArc (K : PocketFaceSet D eps X lo hi)
    {a b : X.toCombMap.Dart} (h : [a, b] <:+: invDarts X K.sourceArc.darts)
    (ha : a ∈ K.boundary.cycle) : RegionMoveCoreCloseTight K a ha := by
  have hinf : [X.toCombMap.alpha b, X.toCombMap.alpha a] <:+: K.sourceArc.darts :=
    regionMoveLoose_infix_reverse_map X.toCombMap.alpha_involutive (l := K.sourceArc.darts) h
  obtain ⟨hb', hba⟩ := regionMoveLoose_next_of_infix_cyclicArc
    (X.faceBoundary (cell X K.source).face).nodup K.sourceArc hinf
  have hnext : K.boundary.cycle.next a ha = b :=
    OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup
      (h.trans K.invDarts_sourceArc_infix) ha
  unfold RegionMoveCoreCloseTight
  rw [hnext, ← OuterPinchCornerFix.facePerm_alpha,
    ← OuterPinchCornerFix.next_faceBoundary_darts (X.faceBoundary (cell X K.source).face) hb']
  exact hba

/-- **Every passage is tight, starts in a side, or starts at a junction**: a passage of the
boundary cycle `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` that is not tight starts in `s₁` or `s₂`, or at the last
dart of `t₁⁻¹` or of `t₂`. -/
theorem regionMoveLoose_tight_or_junction (K : PocketFaceSet D eps X lo hi)
    {e : X.toCombMap.Dart} (he : e ∈ K.boundary.cycle) :
    RegionMoveCoreCloseTight K e he ∨ e ∈ K.firstSide ∨ e ∈ K.secondSide ∨
      (∃ h : invDarts X K.sourceArc.darts ≠ [], e = (invDarts X K.sourceArc.darts).getLast h) ∨
      (∃ h : K.targetArc.darts ≠ [], e = K.targetArc.darts.getLast h) := by
  have hmem := he
  rw [K.decomposition] at hmem
  rcases List.mem_append.mp hmem with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact Or.inr (Or.inl h1)
      · by_cases hl : ∃ h : invDarts X K.sourceArc.darts ≠ [],
            e = (invDarts X K.sourceArc.darts).getLast h
        · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
        · obtain ⟨b, hb⟩ :=
            regionMoveLoose_exists_infix_of_ne_getLast h2 (fun h he' => hl ⟨h, he'⟩)
          exact Or.inl (regionMoveLoose_tight_of_infix_sourceArc K hb he)
    · exact Or.inr (Or.inr (Or.inl h3))
  · by_cases hl : ∃ h : K.targetArc.darts ≠ [], e = K.targetArc.darts.getLast h
    · exact Or.inr (Or.inr (Or.inr (Or.inr hl)))
    · obtain ⟨b, hb⟩ :=
        regionMoveLoose_exists_infix_of_ne_getLast h4 (fun h he' => hl ⟨h, he'⟩)
      exact Or.inl (regionMoveLoose_tight_of_infix_targetArc K hb he)

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_next_of_infix_cyclicArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_infix_reverse_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_exists_infix_of_ne_getLast
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_sigma_eq_of_outerDarts_next
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_tight_of_infix_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_tight_of_infix_sourceArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_tight_or_junction
