import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubSub
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-73: `SUB` from an edge connected outside

* `pinchAbsSub_sub`: `f ∈ side K` and `pinchAbsSub_Outside X K.walk` give `SUB` for EVERY
  boundary circuit of the complement of `pinchAbs_set` (the proof plan is in
  `PinchAbsSubSub.lean`).
* `pinchAbsSub_Rest`: what is left of `pinchAbs_Cut` besides `SUB`, together with the outside
  hypothesis: an edge connected outside of `K.walk`, one dart of `P₀` exposed off `pinchAbs_set`
  (clause (a)), and the tail for every touching circuit (clause (c)).
* `pinchAbsSub_cut_of_rest`: `pinchAbsSub_Rest → pinchAbs_Cut` (through `pinchAbs_cut_of_touch`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`SUB` for every circuit of the complement of `pinchAbs_set`.** -/
theorem pinchAbsSub_sub {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk) (hO : pinchAbsSub_Outside X.toCombMap K.walk)
    (comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f))) :
    sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ⊆
      sideFaces X.toCombMap K.walk := by
  intro h hh
  by_contra hnK
  have hF := pinchAbsSub_set_subset (G₁ := G₁) (G₂ := G₂) (a := a) (b := b) hf
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (FaceSetCircuits.circuit_nonempty X.toCombMap
    (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp)
  have hxw := pinchAbsSub_circuit_not_mem hx
  have hxF : X.toCombMap.faceOf x ∉ pinchAbs_set a b K G₁ G₂ f :=
    (pinchLobe_mem_out _ _ _).mp (pinchCut_isBoundaryDart_of_mem hx).1
  suffices hex : ∃ o, o ∉ sideFaces X.toCombMap K.walk ∧
      (o ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ↔
        X.toCombMap.faceOf x ∈
          sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) by
    obtain ⟨o, ho, hio⟩ := hex
    exact hxw (hio.mp ((pinchAbsSub_out_iff (comp := comp) hF (hO o h ho hnK)).mpr hh))
  rcases Classical.em (X.toCombMap.faceOf x ∈ sideFaces X.toCombMap K.walk) with hs | hs
  · have hr : X.toCombMap.faceOf x ∈ pinchAbs_rest a b K f :=
      pinchAbs_mem_rest.mpr ⟨hs, fun hk => hxF (pinchAbs_keep_subset a b K G₁ G₂ f hk)⟩
    have hre : pinchAbs_Reach a b K G₁ G₂ f (X.toCombMap.faceOf x) :=
      Classical.byContradiction fun hn => hxF (pinchAbs_mem_set.mpr (Or.inr ⟨hr, hn⟩))
    obtain ⟨g₀, hbad, hch⟩ := hre
    obtain ⟨d₀, hd₀, hd₀s, -⟩ := hbad.2
    have ht := pinchAbsSub_transfer (comp := comp) (d := d₀)
      (by rw [hd₀]; exact pinchAbsSub_not_mem_set hbad.1 (pinchAbs_reach_of_bad hbad))
      (fun h' => hd₀s (hF _ h'))
    rw [hd₀] at ht
    exact ⟨_, hd₀s, ht.symm.trans (pinchAbsSub_reach_iff hbad hch)⟩
  · exact ⟨_, hs, Iff.rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_sub

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
