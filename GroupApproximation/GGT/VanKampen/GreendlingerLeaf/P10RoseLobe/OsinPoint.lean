import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinAtLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose lobe chain at one pocket, part 1

Lane gl-p10-74.  The reductions `roseLobeRegion_core_of`, `roseLobeNoBub_place_of` with
`roseLobePlace_blk_of_place`, and `roseLobeBlk_block_of_weak` with
`roseLobeFL_filterListing_of_block` are pointwise: each reads the stronger conclusion at the same
pocket `K`.  Here they are restated at one pocket, with the same proofs:
`roseLobeOsin_coreAt_of` (Region to Core), `roseLobeOsin_blkAt_of` (Core, equal to NoBub, to
Blk) and `roseLobeOsin_filterAt_of` (Blk to the filtered listing).

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

/-- **Region to Core at one pocket**: the proof of `roseLobeRegion_core_of`. -/
theorem roseLobeOsin_coreAt_of (K : PocketFaceSet D eps X lo hi)
    (h : roseLobeOsin_RegionAt K) : roseLobeOsin_CoreAt K := by
  have hc := K.boundary.cycle_mem_iff
  rcases h with
    ⟨rs, hne, hrs, ⟨x, hxk, hx⟩, A, B, C, hb, hp⟩ | ⟨y, hy, hout, hsrcf, A, B, C, hb⟩
  · have hPQ : ∀ d ∈ K.boundary.cycle,
        movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) rs) d = true ↔
        ∀ r ∈ rs, ¬Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) r d :=
      fun d hd => roseLobeRegion_movePred_in hc hrs hd
    have hkx : X.toCombMap.faceOf x ∈ K.faces := by
      rw [hxk]
      exact K.kept_mem
    obtain ⟨hABC, hblk⟩ := roseLobeRegion_block hPQ hb
    refine ⟨rs, Or.inl ⟨hne, hrs⟩, Or.inl fun r hr => ((hc r).mp (hrs r hr)).1, Or.inr ?_,
      A, B, C, hABC, hblk, Or.inr (roseLobeRegion_place hPQ hABC hp)⟩
    rw [← hxk]
    exact (P10Rose.FilterMove.mem_flipFaces_iff (roseJunctionCore_lobeColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) rs) x).mpr
      ⟨fun _ => roseJunctionCore_lobeColour_eq_false _ _ hx, fun _ => hkx⟩
  · have hPQ : ∀ d ∈ K.boundary.cycle,
        movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) [X.toCombMap.alpha y]) d = true ↔
        ¬Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y)
            (X.toCombMap.alpha d) :=
      fun d hd => roseLobeRegion_movePred_out hc hy hd
    have hyo : X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ K.faces := ((hc y).mp hy).2
    obtain ⟨hABC, hblk⟩ := roseLobeRegion_block hPQ hb
    refine ⟨[X.toCombMap.alpha y],
      Or.inr ⟨X.toCombMap.alpha y, rfl, hout, y, hy, Or.inr (Relation.EqvGen.refl _)⟩,
      Or.inr ?_, Or.inl ⟨X.toCombMap.alpha y, rfl, hyo⟩, A, B, C, hABC, hblk,
      Or.inl ⟨X.toCombMap.alpha y, rfl, hyo⟩⟩
    refine P10Rose.FilterMove.not_mem_flipFaces (roseJunctionCore_lobeColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) [X.toCombMap.alpha y]) K.source_not_mem ?_
    intro x hx
    apply roseJunctionCore_lobeColour_eq_false
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hsrcf x hx

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_coreAt_of

/-- **Core to Blk at one pocket**: the proofs of `roseLobeNoBub_place_of` and
`roseLobePlace_blk_of_place`, merged (the positional clauses of Core feed the `Place` sides). -/
theorem roseLobeOsin_blkAt_of (K : PocketFaceSet D eps X lo hi)
    (h : roseLobeOsin_CoreAt K) : roseLobeOsin_BlkAt K := by
  obtain ⟨rs, hroot, hsw, hkw, A, B, C, hABC, hblk, hpos⟩ := h
  have hs := roseLobePlace_src_of K hsw
  refine ⟨rs, hroot, hs, roseLobePlace_kept_of K hkw, ?_, ?_, A, B, C, hABC, hblk⟩
  · rcases hpos with ⟨r, hrs, hr⟩ | ⟨h1, -⟩
    · exact roseLobePlace_place1_of_side K
        (roseJunctionCore_lobeColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)
        (fun d hd => roseLobePlace_lake_eq_false K.boundary.cycle_mem_iff hrs hr hd) hs
    · exact roseLobeNoBub_place1 K hABC hblk h1
  · rcases hpos with ⟨r, hrs, hr⟩ | ⟨-, h2⟩
    · exact roseLobePlace_place2_of_side K
        (fun d hd => roseLobePlace_lake_eq_false K.boundary.cycle_mem_iff hrs hr hd)
        (fun d hd => roseLobePlace_lake_outer K hrs hr hroot hd)
    · exact roseLobeNoBub_place2 K hABC hblk h2

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_blkAt_of

/-- **Blk to the filtered listing at one pocket**: the proofs of `roseLobeBlk_block_of_weak`
and `roseLobeFL_filterListing_of_block`, merged. -/
theorem roseLobeOsin_filterAt_of (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : roseLobeOsin_BlkAt K) : roseLobeOsin_FilterAt K := by
  obtain ⟨rs, hroot, hsource, hkept, hb, ⟨k, hk, hc⟩, A, B, C, hABC, hblk⟩ := h
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hroot' : (∀ r ∈ rs, r ∈ K.boundary.cycle) ∨ ∃ r, rs = [r] := by
    rcases hroot with ⟨-, hrs⟩ | ⟨r, hr, -⟩
    · exact Or.inl hrs
    · exact Or.inr ⟨r, hr⟩
  have hblk' := roseLobeBlk_block_of_side
    (roseJunctionCore_lobeColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)
    (roseLobeBlk_side K.boundary.cycle_mem_iff hroot') hw K.boundary.cycle_nodup hABC hblk
  obtain ⟨t₁, ht₁⟩ := roseLobeFL_exists_arc_invDarts_of_infix X K.sourceArc hb
  obtain ⟨t₂, ht₂, hst, hend⟩ := roseLobeFL_exists_arc_of_prefix_drop K.targetArc hk hc
  exact ⟨rs, hroot, hsource, hkept, ⟨t₁, ht₁⟩, ⟨t₂, ht₂.symm, hst, hend⟩,
    roseLobeFL_isClosedDartWalk_filter_of_block hw hABC hblk'⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_filterAt_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
