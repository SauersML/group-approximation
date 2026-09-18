import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchLobeStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-72: the absorbed lobe set `pinchAbs_set`

Lane gl-p07-71 (`PinchLobeStatement.lean`) reduced `pinchCut_ResidualStatement` to
`pinchLobe_ResidualStatement`, whose new disjunct `pinchLobe_Cut` asks for a face set
`F ⊇ P₀ = keepClass a b K f`, lobe-closed, and a boundary circuit `comp` of its complement with
touch, `SUB` and the tail.  `F = P₀` alone is FALSE (M9, M9big, M11, M11a).  The face set that
passed every check of gl-p07-71 is the ABS construction `m9.absorb` of the truth script.  This
lane defines it in Lean and discharges `P₀ ⊆ F` and the lobe condition for it.

**The construction.**  Write `S = sideFaces K.walk` and `R = S \ P₀` (`pinchAbs_rest`).
* A face `g ∈ R` is *bad* (`pinchAbs_Bad`) when one of its darts `d` has `faceOf (alpha d) ∉ S`
  and `alpha d ∉ G₁ ∪ G₂`: `g` is exposed to the outside of `S` other than along `G₁`/`G₂`.
* Two faces of `R` are *adjacent* (`pinchAbs_Adj`) when they share an edge.
* `pinchAbs_Reach g`: `g` is joined to a bad face by adjacency steps inside `R`.  This is the
  least fixed point of `T ↦ bad ∪ {h ∈ R : h adjacent to T}`, given by `Relation.ReflTransGen`.
* `pinchAbs_set = P₀ ∪ (R \ Reach)`: `P₀` together with every edge component of `R` that has
  no bad face.  This is exactly `m9.absorb` (an edge component `Q` of `R` is absorbed iff each of
  its darts `d` has `faceOf (alpha d) ∈ S` or `alpha d ∈ G`); the script
  `gl-p07-72/abs_check.py` checks the equality `abs_lean == m9.absorb` on every configuration.
  (`m9.absorb` also allows `d ∈ G`; the check shows that never changes the set.)

**Proof of the lobe condition** (`pinchAbs_lobe`, `PinchAbsLemmas.lean`).  Let `faceOf e ∈ F \ P₀`,
so `faceOf e ∈ R` is not reached, and `faceOf (alpha e) ∉ F`; suppose `alpha e ∉ G₁ ∪ G₂`.
* If `faceOf (alpha e) ∉ S`, then `faceOf e` is bad (dart `e`), hence reached: contradiction.
* If `faceOf (alpha e) ∈ S`, it is not in `P₀ ⊆ F`, so it lies in `R`, and it is reached (it is
  not in `F`).  The dart `alpha e` makes it adjacent to `faceOf e`, so `faceOf e` is reached too:
  contradiction.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The rest `R = sideFaces K.walk \ P₀` of the side of the pocket walk. -/
noncomputable def pinchAbs_rest (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (f : X.toCombMap.Face) : Finset X.toCombMap.Face := by
  classical
  exact Finset.univ.filter fun g =>
    g ∈ sideFaces X.toCombMap K.walk ∧ g ∉ FourPieceWitness.keepClass a b K f

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_rest

/-- Membership in the rest. -/
theorem pinchAbs_mem_rest {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {f g : X.toCombMap.Face} :
    g ∈ pinchAbs_rest a b K f ↔
      g ∈ sideFaces X.toCombMap K.walk ∧ g ∉ FourPieceWitness.keepClass a b K f := by
  classical
  unfold pinchAbs_rest
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_mem_rest

/-- A bad face: a face of the rest with a dart whose reversal is off `G₁ ∪ G₂` and based
outside the side of the pocket walk. -/
def pinchAbs_Bad (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f g : X.toCombMap.Face) : Prop :=
  g ∈ pinchAbs_rest a b K f ∧ ∃ d : X.toCombMap.Dart, X.toCombMap.faceOf d = g ∧
    X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ sideFaces X.toCombMap K.walk ∧
    X.toCombMap.alpha d ∉ G₁.darts ∧ X.toCombMap.alpha d ∉ G₂.darts

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_Bad

/-- Two faces of the rest sharing an edge. -/
def pinchAbs_Adj (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (f g h : X.toCombMap.Face) : Prop :=
  g ∈ pinchAbs_rest a b K f ∧ h ∈ pinchAbs_rest a b K f ∧
    ∃ d : X.toCombMap.Dart, X.toCombMap.faceOf d = g ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) = h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_Adj

/-- The faces of the rest joined to a bad face by edge steps inside the rest (the least fixed
point of `T ↦ bad ∪ {h ∈ R : h adjacent to T}`). -/
def pinchAbs_Reach (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f h : X.toCombMap.Face) : Prop :=
  ∃ g, pinchAbs_Bad a b K G₁ G₂ f g ∧ Relation.ReflTransGen (pinchAbs_Adj a b K f) g h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_Reach

/-- **The absorbed lobe set** `P₀ ∪ (R \ Reach)`: the `Q₀`-class `P₀` of `f` and every edge
component of the rest with no bad face. -/
noncomputable def pinchAbs_set (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Finset X.toCombMap.Face := by
  classical
  exact Finset.univ.filter fun g => g ∈ FourPieceWitness.keepClass a b K f ∨
    (g ∈ pinchAbs_rest a b K f ∧ ¬ pinchAbs_Reach a b K G₁ G₂ f g)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_set

/-- Membership in the absorbed lobe set. -/
theorem pinchAbs_mem_set {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {f g : X.toCombMap.Face} :
    g ∈ pinchAbs_set a b K G₁ G₂ f ↔ g ∈ FourPieceWitness.keepClass a b K f ∨
      (g ∈ pinchAbs_rest a b K f ∧ ¬ pinchAbs_Reach a b K G₁ G₂ f g) := by
  classical
  unfold pinchAbs_set
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_mem_set

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
