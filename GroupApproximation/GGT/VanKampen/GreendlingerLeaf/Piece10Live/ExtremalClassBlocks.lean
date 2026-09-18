import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClassChoice
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class: contiguous kept blocks

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-15.

From `ExtremalClassStretches K r`, no two kept darts of an arc are separated by a nonempty run of
removed darts of that arc:

* `targetNoGap_of_classStretches`: the run is also a run of `K.boundary.cycle`, whose ends would
  both lie on the target arc.
* `sourceNoGap_of_classStretches`: reversing the source arc (`invDarts`, `alpha`-invariance of
  `keptPred`), the run becomes a run of `K.boundary.cycle` whose ends both lie on the reversed
  source arc.

With `exists_filter_block_of_noGap` these give contiguous kept blocks.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section ClassBlocks

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **No gap in the kept target darts.** -/
theorem targetNoGap_of_classStretches (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (h : ExtremalClassStretches K r) :
    ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
      (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
      K.targetArc.darts = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
        P10ExtremalResidual.keptPred K r e = true →
        (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) → B = [] := by
  intro A d B e C ht hd he hB
  by_contra hne
  have hc : K.boundary.cycle =
      (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ A) ++
        d :: (B ++ e :: C) := by
    rw [K.decomposition, ht]
    simp only [List.append_assoc]
  have hdm : d ∈ K.targetArc.darts := by
    rw [ht]
    simp
  have hem : e ∈ K.targetArc.darts := by
    rw [ht]
    simp
  exact (h _ d B e C hc hd he hB hne).2.1 ⟨hdm, hem⟩

/-- **No gap in the kept source darts.** -/
theorem sourceNoGap_of_classStretches (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (h : ExtremalClassStretches K r) :
    ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
      (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
      K.sourceArc.darts = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
        P10ExtremalResidual.keptPred K r e = true →
        (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) → B = [] := by
  intro A d B e C hs hd he hB
  by_contra hne
  have hp : ∀ x, P10ExtremalResidual.keptPred K r (X.toCombMap.alpha x) =
      P10ExtremalResidual.keptPred K r x := fun x =>
    P10ExtremalResidual.movePred_alpha X.toCombMap _ x
  have hinv : invDarts X K.sourceArc.darts =
      invDarts X C ++ X.toCombMap.alpha e ::
        (invDarts X B ++ X.toCombMap.alpha d :: invDarts X A) := by
    rw [hs]
    simp only [invDarts, List.reverse_append, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
  have hc : K.boundary.cycle =
      (K.firstSide ++ invDarts X C) ++ X.toCombMap.alpha e ::
        (invDarts X B ++ X.toCombMap.alpha d ::
          (invDarts X A ++ K.secondSide ++ K.targetArc.darts)) := by
    rw [K.decomposition, hinv]
    simp only [List.append_assoc, List.cons_append]
  have hem : X.toCombMap.alpha e ∈ invDarts X K.sourceArc.darts := by
    rw [hinv]
    simp
  have hdm : X.toCombMap.alpha d ∈ invDarts X K.sourceArc.darts := by
    rw [hinv]
    simp
  have hBinv : ∀ x ∈ invDarts X B, P10ExtremalResidual.keptPred K r x = false := by
    intro x hx
    simp only [invDarts, List.mem_map, List.mem_reverse] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hp y).trans (hB y hy)
  have hne' : invDarts X B ≠ [] := by
    intro h0
    exact hne (by simpa [invDarts] using h0)
  exact (h _ (X.toCombMap.alpha e) (invDarts X B) (X.toCombMap.alpha d) _ hc
    ((hp e).trans he) ((hp d).trans hd) hBinv hne').2.2 ⟨hem, hdm⟩

end ClassBlocks

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.targetNoGap_of_classStretches
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.sourceNoGap_of_classStretches
