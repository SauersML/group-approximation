import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose lobe chain at one pocket, part 2

Lane gl-p10-74.  The reductions `roseLobe_lobeRemoval_of_filterListing`,
`P10RoseExtremalTrim.roseJunctionCore_regionMoveSubArc_of_lobeRemoval` and
`P10Rose.inPlaceStep_of_regionMoveSubArc` are pointwise too.  Here they are restated at one
pocket, with the same proofs: `roseLobeOsin_lobeAt_of`, `roseLobeOsin_subArcAt_of` and
`roseLobeOsin_inPlaceAt_of`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The filtered listing to the lobe removal at one pocket**: the proof of
`roseLobe_lobeRemoval_of_filterListing`. -/
theorem roseLobeOsin_lobeAt_of (K : PocketFaceSet D eps X lo hi)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (h : roseLobeOsin_FilterAt K) : roseLobeOsin_LobeAt K := by
  obtain ⟨rs, hcase, hsource, hkept, ⟨t₁, ht₁⟩, ⟨t₂, ht₂, hst, hend⟩, hwalk⟩ := h
  have hfilt := roseLobe_filter_four K.decomposition ht₁ ht₂
  have h₁ := roseLobe_length_le_of_filter_eq ht₁
  have h₂ := roseLobe_length_le_of_filter_eq ht₂
  simp only [roseLobe_length_invDarts, CyclicArc.darts_length] at h₁ h₂
  rw [hfilt] at hwalk
  exact ⟨rs, hcase, K.source, K.kept, hsource, hkept, t₁, t₂, _, _, List.Perm.of_eq hfilt.symm,
    hwalk, (List.length_filter_le _ _).trans K.firstSide_length_le,
    (List.length_filter_le _ _).trans K.secondSide_length_le, K.lo_le.trans hst,
    hend.trans K.le_hi, h₁.trans_lt hsrc, h₂.trans_lt htgt⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_lobeAt_of

/-- **The lobe removal to the sub-arc region move at one pocket**: the proof of
`roseJunctionCore_regionMoveSubArc_of_lobeRemoval`. -/
theorem roseLobeOsin_subArcAt_of (K : PocketFaceSet D eps X lo hi)
    (h : roseLobeOsin_LobeAt K) : roseLobeOsin_SubArcAt K := by
  obtain ⟨rs, hcase, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hwalk,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h
  have hc := K.boundary.cycle_mem_iff
  rcases hcase with ⟨hne, hrs⟩ | ⟨r, rfl, hrout, y, hy, hry⟩
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil rs hne
    exact ⟨roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs,
      roseJunctionCore_lobeColour_step X.toCombMap _ rs,
      fun d hd => Or.inr (roseJunctionCore_lobeColour_alpha_eq_false hc hrs hd),
      roseJunctionCore_not_mem_flipFaces hc hrs K.outerFace_not_mem,
      ⟨r, hrs r hr, roseJunctionCore_movePred_root X.toCombMap _ hr⟩, source, kept, hsource,
      hkept, t₁, t₂, s₁, s₂, hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩
  · rw [roseJunctionCore_lobeColour_singleton] at hsource hkept hperm
    have hz := P10Rose.SubArcMove.regionColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) r
    exact ⟨P10Rose.SubArcMove.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r,
      hz, P10Rose.SubArcMove.regionColour_indep hc r,
      P10Rose.FilterMove.not_mem_flipFaces hz K.outerFace_not_mem
        (fun x hx => P10Rose.SubArcMove.regionColour_eq_false X.toCombMap _ (hrout x hx)),
      ⟨y, hy, P10Rose.SubArcMove.movePred_regionColour_eq_false hry⟩, source, kept, hsource,
      hkept, t₁, t₂, s₁, s₂, hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_subArcAt_of

/-- **The sub-arc region move to the in-place step at one pocket**: the proof of
`P10Rose.inPlaceStep_of_regionMoveSubArc`, by `P10Rose.step_of_faces`. -/
theorem roseLobeOsin_inPlaceAt_of (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.ClosedWalk)
    (h : roseLobeOsin_SubArcAt K) : roseLobeOsin_InPlaceAt K := by
  obtain ⟨z, hz, hind, hout, ⟨y, hy, hpy⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hLperm,
    hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hbd := P10Rose.FilterMove.isBoundaryDart_flipFaces_iff K.boundary.cycle_mem_iff hz hind
  have hmem : ∀ d, d ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap (flipFaces X.toCombMap K.faces z) d :=
    fun d => (hLperm.mem_iff.trans List.mem_filter).trans (hbd d).symm
  have hperm : List.Perm K.boundary.cycle ((s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ++
      K.boundary.cycle.filter (fun d => !movePred X.toCombMap z d)) :=
    (List.filter_append_perm (movePred X.toCombMap z) K.boundary.cycle).symm.trans
      (hLperm.symm.append_right _)
  have hneL : s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] := by
    obtain ⟨hne, -⟩ := hwalk
    exact hne
  have hx₀ := List.mem_filter.mp (hLperm.mem_iff.mp (List.head_mem hneL))
  obtain ⟨A, B, hne, hAB, hlast, hhead⟩ :=
    P10Rose.FilterWalk.exists_rotation (movePred X.toCombMap z) hx₀.1 hx₀.2 hy hpy
  have hwAB : IsClosedDartWalk X.toCombMap (A ++ B) := by
    rw [← hAB]
    exact hw
  obtain ⟨_hne', -, hclose⟩ := hwAB.append_comm
  have hmemc : ∀ d ∈ B ++ A, d ∈ K.boundary.cycle := by
    intro d hd
    rw [hAB]
    exact List.mem_append.mpr (List.mem_append.mp hd).symm
  have he : (B ++ A).getLast hne ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts :=
    hLperm.mem_iff.mpr (List.mem_filter.mpr ⟨hmemc _ (List.getLast_mem hne), hlast⟩)
  obtain ⟨x, hx, hxv⟩ := P10Rose.exists_succ_of_isClosedDartWalk hwalk he
  have hy' : (B ++ A).head hne ∈ K.boundary.cycle.filter (fun d => !movePred X.toCombMap z d) :=
    List.mem_filter.mpr ⟨hmemc _ (List.head_mem hne), by simp only [hhead, Bool.not_false]⟩
  exact P10Rose.step_of_faces K hlabel hout hsource hkept hmem hs₁ hs₂ hlo hhi ht₁ ht₂ hwalk
    hperm hx hy' (hxv.symm.trans hclose)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_inPlaceAt_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
