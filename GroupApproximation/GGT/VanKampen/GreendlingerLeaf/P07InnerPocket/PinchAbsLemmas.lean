import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-72: `P₀ ⊆ F`, the lobe condition and touch for `pinchAbs_set`

For `F = pinchAbs_set a b K G₁ G₂ f` (`PinchAbsDef.lean`):
* `pinchAbs_keep_subset`: `P₀ = keepClass a b K f ⊆ F`, unconditionally.
* `pinchAbs_lobe`: the lobe condition of `pinchLobe_Cut` / `pinchCut_Cut`, unconditionally: a dart
  based in `F \ P₀` whose reversal is based off `F` is the reversal of a `G₁`/`G₂` dart.  The
  proof is the two-case argument of the `PinchAbsDef.lean` docstring.
* `pinchAbs_touch_of_dart` / `pinchAbs_dart_of_touch`: for any `P ⊆ F`, the touch clause of
  `pinchLobe_Cut` (some complement circuit has a dart whose reversal is based in `P`) holds iff
  some dart based in `P` has its reversal based off `F`.  So the touch clause is a statement
  about one dart; the circuit is the one through its reversal.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`P₀ ⊆ F`.** -/
theorem pinchAbs_keep_subset (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face) :
    FourPieceWitness.keepClass a b K f ⊆ pinchAbs_set a b K G₁ G₂ f := by
  intro g hg
  exact pinchAbs_mem_set.mpr (Or.inl hg)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_keep_subset

/-- A bad face is reached. -/
theorem pinchAbs_reach_of_bad {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {f g : X.toCombMap.Face} (hg : pinchAbs_Bad a b K G₁ G₂ f g) :
    pinchAbs_Reach a b K G₁ G₂ f g :=
  ⟨g, hg, Relation.ReflTransGen.refl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_reach_of_bad

/-- A face of the rest adjacent to a reached face is reached. -/
theorem pinchAbs_reach_step {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {f g h : X.toCombMap.Face} (hg : pinchAbs_Reach a b K G₁ G₂ f g)
    (hadj : pinchAbs_Adj a b K f g h) : pinchAbs_Reach a b K G₁ G₂ f h := by
  obtain ⟨g₀, hb, hr⟩ := hg
  exact ⟨g₀, hb, hr.tail hadj⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_reach_step

/-- **The lobe condition for the absorbed lobe set.** -/
theorem pinchAbs_lobe (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face) :
    ∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ pinchAbs_set a b K G₁ G₂ f →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K f →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ pinchAbs_set a b K G₁ G₂ f →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts := by
  intro e he hne hout
  rcases pinchAbs_mem_set.mp he with hk | ⟨hrest, hnr⟩
  · exact absurd hk hne
  refine Classical.byContradiction fun hG => ?_
  obtain ⟨h₁, h₂⟩ := not_or.mp hG
  rcases Classical.em (X.toCombMap.faceOf (X.toCombMap.alpha e) ∈
      sideFaces X.toCombMap K.walk) with hs | hs
  · have hnk : X.toCombMap.faceOf (X.toCombMap.alpha e) ∉
        FourPieceWitness.keepClass a b K f :=
      fun hk => hout (pinchAbs_mem_set.mpr (Or.inl hk))
    have hr' : X.toCombMap.faceOf (X.toCombMap.alpha e) ∈ pinchAbs_rest a b K f :=
      pinchAbs_mem_rest.mpr ⟨hs, hnk⟩
    have hreach : pinchAbs_Reach a b K G₁ G₂ f (X.toCombMap.faceOf (X.toCombMap.alpha e)) :=
      Classical.byContradiction fun hn => hout (pinchAbs_mem_set.mpr (Or.inr ⟨hr', hn⟩))
    have hadj : pinchAbs_Adj a b K f (X.toCombMap.faceOf (X.toCombMap.alpha e))
        (X.toCombMap.faceOf e) :=
      ⟨hr', hrest, X.toCombMap.alpha e, rfl,
        congrArg X.toCombMap.faceOf (X.toCombMap.alpha_involutive e)⟩
    exact hnr (pinchAbs_reach_step hreach hadj)
  · exact hnr (pinchAbs_reach_of_bad ⟨hrest, e, rfl, hs, h₁, h₂⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_lobe

/-- **Touch from one dart.**  A dart based in `P ⊆ F` whose reversal is based off `F` gives a
boundary circuit of the complement of `F` touching `P`: the circuit through the reversal. -/
theorem pinchAbs_touch_of_dart {M : CombMap.{v}} {P F : Finset M.Face} (hPF : P ⊆ F)
    {y : M.Dart} (hy : M.faceOf y ∈ P) (hyF : M.faceOf (M.alpha y) ∉ F) :
    ∃ comp : FaceSetCircuits.Component M (pinchLobe_out M F),
      ∃ x ∈ FaceSetCircuits.circuit M (pinchLobe_out M F) comp, M.faceOf (M.alpha x) ∈ P := by
  have hbd : Surgery.MapCollapse.IsBoundaryDart M (pinchLobe_out M F) (M.alpha y) := by
    refine ⟨(pinchLobe_mem_out M F _).mpr hyF, ?_⟩
    rw [M.alpha_involutive y, pinchLobe_mem_out M F]
    exact fun h => h (hPF hy)
  refine ⟨Quotient.mk'' ⟨M.alpha y, hbd⟩, M.alpha y,
    (FaceSetCircuits.mem_circuit_iff M (pinchLobe_out M F) _ _).mpr ⟨hbd, rfl⟩, ?_⟩
  rw [M.alpha_involutive y]
  exact hy

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_touch_of_dart

/-- **One dart from touch** (the converse of `pinchAbs_touch_of_dart`). -/
theorem pinchAbs_dart_of_touch {M : CombMap.{v}} {P F : Finset M.Face}
    {comp : FaceSetCircuits.Component M (pinchLobe_out M F)} {x : M.Dart}
    (hx : x ∈ FaceSetCircuits.circuit M (pinchLobe_out M F) comp)
    (hxP : M.faceOf (M.alpha x) ∈ P) :
    ∃ y : M.Dart, M.faceOf y ∈ P ∧ M.faceOf (M.alpha y) ∉ F := by
  refine ⟨M.alpha x, hxP, ?_⟩
  rw [M.alpha_involutive x]
  exact (pinchLobe_mem_out M F _).mp (pinchCut_isBoundaryDart_of_mem hx).1

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_dart_of_touch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
