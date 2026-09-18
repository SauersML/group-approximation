import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-78: the pinched case (`¬ FollowsBoundary`)

## LOUD: the pinched half `pinchAbsFol_PinchPart` is FALSE

The lane target is `pinchAbsFol_PinchPart` (`PinchAbsFolParts.lean`), whose conclusion is
`pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbs_Cut a b K G₁ G₂ C.face` under
`¬ (hw.outerCycle X.planar).FollowsBoundary`.  It fails on the pinch model of
`Manuscript/NonMF/Full/GL03BPinch/Statement.lean` (48 darts, `V = 18`, `E = 24`, `F = 8`,
`χ = 2`; faces `Π_i`, `C`, `Π_j`, `H₁`, `H₂`, `a`, `b`, `o`).  Checked by script against the Lean
conventions (`σ d = facePerm (α d)`, edge based `walkKeep`, `sideFaces` as the class of the walk
darts, `EnclosedFaceSetSucc` with bridge pairs):
* `K` is noncrossing, `side K = {C, H₁, H₂, a, b}` (outer face `o` off it), both reclosed Euler
  characteristics are `2`, the outer cycle does NOT follow its boundary, the inner one does;
* `keepClass = witnessFaces = pinchAbs_set = {C, H₁, H₂}`; the complement has three boundary
  circuits (`[a, b]`, `[Π_i]`, `[Π_j]`), all touch `keepClass`, and every `w'` has a face off
  `side K` (`Π_i`/`Π_j` for the first, `o` for the other two).  So `pinchAbs_Cut` is FALSE;
* 9777 successor form enclosed pairs contain `C`; none meets disjunct 1 of
  `pinchFollow_Conclusion` (the only dart clause pass is `{C, H₁, H₂, Π_i, Π_j} ⊄ side K`), and
  disjunct 2 is impossible.  So `pinchFollow_Conclusion` is FALSE;
* `hcase` holds (the arcs of `a`, `b` are empty) and `hP` is vacuous (`witnessFaces` has no
  successor form walk).
Hence `pinchAbsFol_PinchPart` is FALSE, and with it (`pinchAbsFol_pinchPart_of_res`)
`pinchAbsFol_ResidualStatement` and the equivalent `pinchAbsOut_ResidualStatement`.  No true
strictly weaker residual can reduce to it, so none is defined here.  (Assumed, as the upstream
file asserts: the model is realised as a `DiscDiagram` with `RegionCandidate`s of empty arcs.)

The suggested decomposition of `K.walk` at its repeated vertex also fails: the three sub-walks
`∂Π_i⁻¹`, `∂Π_j⁻¹`, `s₂ s₁` have sides containing `o`, `o`, and `Π_i, Π_j`; `side K` is their
intersection, so no sub-walk has its side inside `side K`.  The upstream corrected disjunct
(`InnerPocketEnclosedTwoArcCorrected`: all relator cells enclosed, walk length `≤ 2 ε`) HOLDS on
the model (the inner disc, walk `[s₁⁻, s₂⁻]`); the correction belongs at the top target.

## What is proved (reusable, true)

* `pinchAbsPinch_Link comp`: every face off `side K` is joined, by faces off `side K` sharing
  edges, to the face of some dart of the circuit `comp`.  A per circuit replacement for the
  global `pinchAbsSub_Outside`; it FAILS in the model, as it must.
* `pinchAbsPinch_sub_of_link`: `f ∈ side K → pinchAbsPinch_Link comp → SUB` for `comp`.
* `pinchAbsPinch_cut_of_link`: link and tail for every touching circuit, plus one exposed dart
  of `P₀`, give `pinchAbs_Cut`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Per circuit outside link.**  Every face off the side of `K.walk` is joined by an outside
chain to the face of a dart of the circuit `comp`. -/
def pinchAbsPinch_Link (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face)
    (comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f))) : Prop :=
  ∀ h : X.toCombMap.Face, h ∉ sideFaces X.toCombMap K.walk →
    ∃ x ∈ FaceSetCircuits.circuit X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp,
      Relation.ReflTransGen (pinchAbsSub_OutAdj X.toCombMap K.walk) (X.toCombMap.faceOf x) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinch_Link

/-- **`SUB` from the link.** -/
theorem pinchAbsPinch_sub_of_link {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk)
    {comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f))}
    (hl : pinchAbsPinch_Link a b K G₁ G₂ f comp) :
    sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp) ⊆
      sideFaces X.toCombMap K.walk := by
  intro h hh
  by_contra hnK
  obtain ⟨x, hx, hc⟩ := hl h hnK
  have hF := pinchAbsSub_set_subset (G₁ := G₁) (G₂ := G₂) (a := a) (b := b) hf
  exact pinchAbsSub_circuit_not_mem hx ((pinchAbsSub_out_iff (comp := comp) hF hc).mpr hh)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinch_sub_of_link

/-- **The absorbed lobe cut from the link.**  Link and tail for every touching circuit, and one
dart of `P₀` whose reversal is based off `pinchAbs_set`. -/
theorem pinchAbsPinch_cut_of_link {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk)
    (hrest : ∀ comp : FaceSetCircuits.Component X.toCombMap
        (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)),
      (∃ x ∈ FaceSetCircuits.circuit X.toCombMap
          (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ f)) comp,
        X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f) →
      pinchAbsPinch_Link a b K G₁ G₂ f comp ∧
      (EnclosedFaceSetSucc X
          (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))
          (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp)) →
        pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ f) comp))))
    {y : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ FourPieceWitness.keepClass a b K f)
    (hyF : X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ pinchAbs_set a b K G₁ G₂ f) :
    pinchAbs_Cut a b K G₁ G₂ f :=
  pinchAbs_cut_of_touch
    (fun comp ht => ⟨pinchAbsPinch_sub_of_link hf (hrest comp ht).1, (hrest comp ht).2⟩) hy hyF

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinch_cut_of_link

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
