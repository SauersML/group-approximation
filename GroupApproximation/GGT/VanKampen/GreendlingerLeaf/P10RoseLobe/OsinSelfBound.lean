import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinSelfPiece
import GroupApproximation.Meta.AxiomGuard

/-!
# The all-pairs shared-arc bound

Lane gl-p10-81.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

* `roseLobeOsinSelf_SharedArcBoundAll X μ`: `roseLobeOsinPiece_SharedArcBound X μ` without the
  hypothesis `i ≠ j`.  An arc `a :: A` read forwards on cell `i` and backwards on cell `j`
  (possibly the same cell) has fewer than `μ · |cell i|` darts.
* `roseLobeOsinSelf_NonGenericBound X μ`: the same bound, only for `i = j` and only when the
  overlap is non-generic, `listVal v' = listVal v` (notation of `OsinSelfPiece`).
* `roseLobeOsinSelf_sharedArcBound`: the cell bounds, least area and the non-generic bound give
  the all-pairs bound.  Case split:
  * generic overlap: `roseLobeOsinSelf_genArc_lt` (any `i`, `j`);
  * non-generic, `i ≠ j`: `roseLobeOsinPiece_sharedArc_lt` (least area; its genericity is
    proved there by the two-cell surgery);
  * non-generic, `i = j`: the hypothesis.
* `roseLobeOsinSelf_pairs_of_all`: the all-pairs bound gives the distinct-pairs one.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- **The all-pairs shared-arc bound** of a diagram `X`: an arc `a :: A` read forwards on
relator cell `i` and backwards on relator cell `j` (where `i = j` is allowed) has fewer than
`μ · |cell i|` darts. -/
def roseLobeOsinSelf_SharedArcBoundAll {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W) (mu : ℝ) : Prop :=
  ∀ i j : Fin X.rCellCount, ∀ (n m : ℕ) (a : X.toCombMap.Dart)
    (A S T : List X.toCombMap.Dart), (cellDarts X i).rotate n = a :: (A ++ S) →
      (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha →
        ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_SharedArcBoundAll

/-- **The non-generic self-overlap bound** of a diagram `X`: if relator cell `i` reads the arc
`a :: A` forwards (rotation `n`) and backwards (rotation `m`), and the overlap is non-generic,
`listVal (revInv ℓ(rotate m (cell i))) = listVal ℓ(a :: (A ++ S))`, then the arc has fewer
than `μ · |cell i|` darts. -/
def roseLobeOsinSelf_NonGenericBound {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W) (mu : ℝ) : Prop :=
  ∀ (i : Fin X.rCellCount) (n m : ℕ) (a : X.toCombMap.Dart)
    (A S T : List X.toCombMap.Dart), (cellDarts X i).rotate n = a :: (A ++ S) →
      (cellDarts X i).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha →
        RelLetter.listVal
            (HullSC.RelWord.revInv (dartWord X ((cellDarts X i).rotate m))) =
          RelLetter.listVal (dartWord X (a :: (A ++ S))) →
          ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_NonGenericBound

/-- **The all-pairs shared-arc bound** from the cell bounds, least area and the non-generic
self-overlap bound. -/
theorem roseLobeOsinSelf_sharedArcBound {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (hlea : X.LeastArea)
    (hN : roseLobeOsinSelf_NonGenericBound X mu) :
    roseLobeOsinSelf_SharedArcBoundAll X mu := by
  intro i j n m a A S T hi hj
  by_cases hgen : RelLetter.listVal
      (HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m))) =
    RelLetter.listVal (dartWord X (a :: (A ++ S)))
  · by_cases hij : i = j
    · subst hij
      exact hN _ n m a A S T hi hj hgen
    · exact roseLobeOsinPiece_sharedArc_lt hB hlea hij hi hj
  · exact roseLobeOsinSelf_genArc_lt hB hi hj hgen

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_sharedArcBound

/-- The all-pairs bound gives the distinct-pairs bound `roseLobeOsinPiece_SharedArcBound`. -/
theorem roseLobeOsinSelf_pairs_of_all {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W} {mu : ℝ}
    (h : roseLobeOsinSelf_SharedArcBoundAll X mu) :
    roseLobeOsinPiece_SharedArcBound X mu :=
  fun i j _ n m a A S T hi hj => h i j n m a A S T hi hj

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_pairs_of_all

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
