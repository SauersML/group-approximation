import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-73: `SUB` for every circuit of the complement of ABS

`pinchAbsSub_Outside M w`: any two faces off `sideFaces M w` are joined by a chain of faces off
the side, consecutive ones sharing an edge.

**`pinchAbsSub_sub`.**  Let `F = pinchAbs_set a b K G₁ G₂ f` with `f ∈ side K`, so `F ⊆ side K`
(`pinchAbsSub_set_subset`).  Assume `pinchAbsSub_Outside X K.walk`.  Then for EVERY boundary
circuit `comp` of the complement of `F`, `side w' ⊆ side K` with `w' = pinchLobe_walk F comp`.
Suppose `h ∈ side w'` and `h ∉ side K`.  Take a dart `x` of the circuit (`circuit_nonempty`); its
face `g` is off `F` and off `side w'` (`pinchAbsSub_circuit_not_mem`).  Find a face `o` off
`side K` on the same side of `w'` as `g`:
* if `g ∉ side K`, take `o = g`;
* otherwise `g` is in the rest (it is off `P₀ ⊆ F`) and reached (it is off `F`), so a reach chain
  runs from a bad face `g₀` to `g`, all of whose faces are reached and so off `F`
  (`pinchAbsSub_reach_iff`); the bad dart `d₀` of `g₀` crosses an edge with both faces off `F` to
  `o = faceOf (alpha d₀) ∉ side K` (`pinchAbsSub_transfer`).
Then `pinchAbsSub_Outside` joins `o` to `h` off `side K ⊇ F` (`pinchAbsSub_out_iff`), so `h` and
`g` are on the same side of `w'`: contradiction.

**`pinchAbsSub_sealed`** (towards clause (a)): if no dart of `P₀` has its reversal based off `F`,
every boundary dart of `F` is the reversal of a `G₁`/`G₂` dart (`pinchAbs_lobe`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The outside of `w` is edge connected.** -/
def pinchAbsSub_Outside (M : CombMap.{v}) (w : List M.Dart) : Prop :=
  ∀ g h : M.Face, g ∉ sideFaces M w → h ∉ sideFaces M w →
    Relation.ReflTransGen (pinchAbsSub_OutAdj M w) g h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_Outside

/-- `pinchAbs_set ⊆ sideFaces K.walk` when `f ∈ sideFaces K.walk`. -/
theorem pinchAbsSub_set_subset {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk) :
    ∀ g, g ∈ pinchAbs_set a b K G₁ G₂ f → g ∈ sideFaces X.toCombMap K.walk := by
  intro g hg
  rcases pinchAbs_mem_set.mp hg with hk | ⟨hr, -⟩
  · exact PocketClass.mem_sideFaces_of_mem_pocketClass hf (pinchCut_mem_pocketClass hk)
  · exact (pinchAbs_mem_rest.mp hr).1

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_set_subset

/-- A reached face of the rest is off `pinchAbs_set`. -/
theorem pinchAbsSub_not_mem_set {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f g : X.toCombMap.Face}
    (hr : g ∈ pinchAbs_rest a b K f) (hre : pinchAbs_Reach a b K G₁ G₂ f g) :
    g ∉ pinchAbs_set a b K G₁ G₂ f := by
  intro hg
  rcases pinchAbs_mem_set.mp hg with hk | ⟨-, hn⟩
  · exact (pinchAbs_mem_rest.mp hr).2 hk
  · exact hn hre

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_not_mem_set

/-- **Transfer along a reach chain.** -/
theorem pinchAbsSub_reach_iff {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f g₀ h : X.toCombMap.Face}
    {comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f))}
    (hbad : pinchAbs_Bad a b K G₁ G₂ f g₀)
    (hc : Relation.ReflTransGen (pinchAbs_Adj a b K f) g₀ h) :
    g₀ ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ↔
      h ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) := by
  induction hc with
  | refl => exact Iff.rfl
  | @tail b' c' hab hbc ih =>
      have hrb : pinchAbs_Reach a b K G₁ G₂ f b' := ⟨g₀, hbad, hab⟩
      have hrc : pinchAbs_Reach a b K G₁ G₂ f c' := ⟨g₀, hbad, hab.tail hbc⟩
      obtain ⟨hbr, hcr, d, hdb, hdc⟩ := hbc
      have key := pinchAbsSub_transfer (comp := comp) (d := d)
        (by rw [hdb]; exact pinchAbsSub_not_mem_set hbr hrb)
        (by rw [hdc]; exact pinchAbsSub_not_mem_set hcr hrc)
      rw [hdb, hdc] at key
      exact ih.trans key

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_reach_iff

/-- **Sealed or touching** (towards clause (a)). -/
theorem pinchAbsSub_sealed (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face)
    (hno : ¬ ∃ y : X.toCombMap.Dart,
      X.toCombMap.faceOf y ∈ FourPieceWitness.keepClass a b K f ∧
        X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ pinchAbs_set a b K G₁ G₂ f)
    (e : X.toCombMap.Dart) (he : X.toCombMap.faceOf e ∈ pinchAbs_set a b K G₁ G₂ f)
    (he' : X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ pinchAbs_set a b K G₁ G₂ f) :
    X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts :=
  pinchAbs_lobe a b K G₁ G₂ f e he (fun hk => hno ⟨e, hk, he'⟩) he'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_sealed

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
