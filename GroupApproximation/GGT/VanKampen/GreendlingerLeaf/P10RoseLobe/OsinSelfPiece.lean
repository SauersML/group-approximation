import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPieceStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs a relator cell shares with itself

Lane gl-p10-81.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The configuration

Relator cells `i`, `j` of a disc diagram `X` (now allowing `i = j`).  Cell `i` rotated by `n`
reads `a :: (A ++ S)`, and cell `j` rotated by `m` reads `T ++ (a :: A).reverse.map α`.
Write `v = ℓ(a :: (A ++ S))` and `v' = revInv ℓ(rotate m (cell j))`.  Then `v'` starts
with `ℓ(a :: A)`.

## Generic overlaps are pieces: `roseLobeOsinSelf_isPiece_gen`

If `listVal v' ≠ listVal v`, then `ℓ(a :: A)` is an `ε`-piece of `v`, with witness `v'`,
`u' = ℓ(a :: A)`, `y = z = 1`.  This is the proof of `roseLobeOsinPiece_isPiece` with the
genericity supplied directly instead of from the two-cell surgery, so it needs neither `i ≠ j`
nor least area.  Under the cell bounds the `pieces` clause then gives
`|a :: A| < μ · |cell i|` (`roseLobeOsinSelf_genArc_lt`).

## The non-generic self overlaps

What is left is `i = j` with `listVal v' = listVal v` (for `i ≠ j` this case is excluded by
least area, `roseLobeOsinPiece_merge_ne_one`).  That is `roseLobeOsinSelf_NonGenericBound`.

**LOUD: it is NOT automatic.**  Planarity (truth check part 1) makes every edge of a
self-shared arc a bridge, so the cell word reads cyclically `w X w⁻¹ Y`, with `X` the closed
walk around the side `C₂` of the bridge path that holds no outer face.  With
`h = val(w X w⁻¹)`, `y = val Y`, `g = h y`, non-genericity is `h y = h⁻¹ y⁻¹`, i.e.
`g = y g⁻¹ y⁻¹`.

* In a free group this forces `g = 1` (truth check part 2), excluded by qg + long.
* With torsion it does not: in `D∞ = ⟨s, t | s², t²⟩`, `h = s t s`, `y = s` gives
  `g = s t` of infinite order (truth check part 3).  So the genericity clause of `IsPiece`
  really can fail at a self overlap, and the arc is then not certified as a piece.
* If `C₂` holds no relator cell, `val X = 1`, so the arc `w X w⁻¹` has value `1` and qg gives
  `2 λ |w| ≤ c`, a bounded length.  If `C₂` holds relator cells, the expected argument is
  Greendlinger's lemma on the least-area sub-diagram `C₂` whose boundary `X` is a qg arc of the
  cell.  That is an induction on area inside the main theorem, not a local lemma, so it is
  left as the residual.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- **A generic shared arc is a piece** (any cells `i`, `j`, possibly equal).  Cell `i`
rotated by `n` reads `a :: (A ++ S)` and cell `j` rotated by `m` reads
`T ++ (a :: A).reverse.map α`.  If `revInv ℓ(rotate m (cell j))` and `ℓ(a :: (A ++ S))` have
different values, then `ℓ(a :: A)` is an `ε`-piece of `ℓ(a :: (A ++ S))`. -/
theorem roseLobeOsinSelf_isPiece_gen {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} (eps : ℕ)
    (hinv : ∀ word ∈ W, HullSC.RelWord.revInv word ∈ W)
    (hrot : ∀ word ∈ W, ∀ n : ℕ, word.rotate n ∈ W)
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    {n m : ℕ} {a : X.toCombMap.Dart} {A S T : List X.toCombMap.Dart}
    (hi : (cellDarts X i).rotate n = a :: (A ++ S))
    (hj : (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha)
    (hgen : RelLetter.listVal
        (HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m))) ≠
      RelLetter.listVal (dartWord X (a :: (A ++ S)))) :
    HullSC.RelWord.IsPiece D W eps (dartWord X (a :: A)) (dartWord X (a :: (A ++ S))) := by
  have hvS : dartWord X (a :: (A ++ S)) = dartWord X (a :: A) ++ dartWord X S := by
    rw [← List.cons_append, Embedded.dartWord_append]
  have hv'eq : HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m)) =
      dartWord X (a :: A) ++ HullSC.RelWord.revInv (dartWord X T) := by
    rw [hj, Embedded.dartWord_append, HullSC.RelWord.revInv_append,
      Embedded.dartWord_reverse_alpha, HullSC.RelWord.revInv_revInv]
  have hvW : dartWord X (a :: (A ++ S)) ∈ W := by
    rw [← hi, roseLobeOsinPiece_dartWord_rotate, dartWord_cellDarts]
    exact hrot _ (cell X i).word_mem n
  have hv'W : HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m)) ∈ W := by
    rw [roseLobeOsinPiece_dartWord_rotate, dartWord_cellDarts]
    exact hinv _ (hrot _ (cell X j).word_mem m)
  exact ⟨hvW, ⟨_, hvS⟩, _, hv'W, fun h => hgen (congrArg RelLetter.listVal h), _, _, hv'eq,
    1, 1, (WordMetric.wordNorm_one _).trans_le (Nat.zero_le _),
    (WordMetric.wordNorm_one _).trans_le (Nat.zero_le _), by rw [one_mul, mul_one],
    by simpa only [one_mul, inv_one, mul_one] using hgen⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_isPiece_gen

/-- **A generic shared arc is short** (any cells `i`, `j`, possibly equal): under the cell
bounds, `|a :: A| < μ · |cell i|`. -/
theorem roseLobeOsinSelf_genArc_lt {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho)
    {i j : Fin X.rCellCount} {n m : ℕ} {a : X.toCombMap.Dart}
    {A S T : List X.toCombMap.Dart}
    (hi : (cellDarts X i).rotate n = a :: (A ++ S))
    (hj : (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha)
    (hgen : RelLetter.listVal
        (HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m))) ≠
      RelLetter.listVal (dartWord X (a :: (A ++ S)))) :
    ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ) := by
  have h := hB.2.2.2.2 _ _ (roseLobeOsinSelf_isPiece_gen eps hB.1 hB.2.1 hi hj hgen)
  have hu : (dartWord X (a :: A)).length = (a :: A).length := List.length_map _
  have hv : (dartWord X (a :: (A ++ S))).length = (cellDarts X i).length := by
    rw [← hi, roseLobeOsinPiece_dartWord_rotate, List.length_rotate]
    exact List.length_map _
  rw [hu, hv] at h
  exact h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_genArc_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
