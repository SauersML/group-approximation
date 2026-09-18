import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-40: a turn of the outside walk along a cell

Lane gl-p07-40.  Certifies no printed sentence on its own.

* `witnessStep_facePerm_of_rotate`: if `d, d'` are consecutive in a rotation of an outside walk
  `ow` that turns to its successor (`EnclosedFaceSetSucc`), and the face successor of `d` is an
  edge of `ow`, then `d' = facePerm d`.  This is `PocketRun.succ_eq_facePerm_of_keep` moved to
  the rotation by `ArcClose.rotate_step`.
* `witnessStep_alpha_eq_of_cellTurn`: let `(x, y)` be consecutive in a rotation of the inverse
  walk `l = invDarts X ow`.  Then `(α y, α x)` is consecutive in a rotation of `ow`
  (`witnessStep_rotate_of_rotate_inv`).  If `α y` is followed on a cell arc by a dart `g` of
  `ow`, then `facePerm (α y) = g` (the arc is a face chain) and `g` is kept.  So `g = α x`.
* `witnessStep_curve_eq_append`: the curve word is `Ḡ₁ ++ (Ā ++ Ḡ₂' ++ B̄)`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section StepTurn

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A kept face successor is the next dart of any rotation of the outside walk.** -/
theorem witnessStep_facePerm_of_rotate {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {m : ℕ}
    {s t : List X.toCombMap.Dart} {d d' : X.toCombMap.Dart}
    (h : ow.rotate m = s ++ d :: d' :: t)
    (hkeep : walkKeep X.toCombMap ow (X.toCombMap.facePerm d)) :
    X.toCombMap.facePerm d = d' := by
  have hlen : s.length + 1 < (ow.rotate m).length := by
    rw [h, List.length_append, List.length_cons, List.length_cons]
    omega
  have hpos : 0 < ow.length := by
    rw [← List.length_rotate ow m]
    omega
  have hp : (s.length + m) % ow.length < ow.length := Nat.mod_lt _ hpos
  have e0 : (ow.rotate m)[s.length]'(by omega) = d := List.getElem_of_append h rfl
  have h' : ow.rotate m = (s ++ [d]) ++ d' :: t := by simp [h]
  have e1 : (ow.rotate m)[s.length + 1]'hlen = d' := List.getElem_of_append h' (by simp)
  have hq : ow[(s.length + m) % ow.length]'hp = d := by
    rw [← e0, List.getElem_rotate]
  have hstep := PocketRun.succ_eq_facePerm_of_keep E _ hp (by rw [hq]; exact hkeep)
  have hrs := ArcClose.rotate_step ow m s.length hlen hp hstep
  rw [← e0, ← e1]
  exact hrs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_facePerm_of_rotate

/-- **A turn of the inverse walk along a cell arc.**  If `(x, y)` is consecutive in a rotation of
`invDarts X ow`, and `α y` is followed on a cell arc by a dart `g` of `ow`, then `g = α x`. -/
theorem witnessStep_alpha_eq_of_cellTurn {k : Fin X.rCellCount} {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {n : ℕ}
    {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {Γ : CyclicArc (cellDarts X k)} {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hG : Γ.darts = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow) :
    g = X.toCombMap.alpha x := by
  have h0 : (ow.reverse.map X.toCombMap.alpha).rotate n = s ++ x :: y :: t := h
  have hr := witnessStep_rotate_of_rotate_inv X.toCombMap.alpha_involutive h0
  have hchain : X.toCombMap.facePerm (X.toCombMap.alpha y) = g :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp
      (PocketRun.arcDarts_isChain (X.faceBoundary (cell X k).face) Γ) hG
  have hkeep : walkKeep X.toCombMap ow (X.toCombMap.facePerm (X.toCombMap.alpha y)) := by
    rw [hchain]
    exact Or.inl hg
  exact hchain.symm.trans (witnessStep_facePerm_of_rotate E hr hkeep)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_alpha_eq_of_cellTurn

/-- **The curve word splits after its first block.** -/
theorem witnessStep_curve_eq_append (a b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) :
    witnessSublistCurve a b G₁ G₂ = invDarts X G₁.darts ++
      (FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
        FourBlock.sideBWord b G₁ G₂) := by
  unfold witnessSublistCurve
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_curve_eq_append

end StepTurn

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
