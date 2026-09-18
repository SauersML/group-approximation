import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPieceMerge
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinCoreBounds
import GroupApproximation.Meta.AxiomGuard

/-!
# A shared arc of two relator cells of a least-area diagram is a piece

Lane gl-p10-79.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The configuration

Take distinct relator cells `i ≠ j` of a disc diagram `X` over `W`, sharing the arc
`a :: A`: cell `i`, rotated by `n`, reads `a :: (A ++ S)`, and cell `j`, rotated by `m`, reads
`T ++ (a :: A).reverse.map α`.  So cell `j` runs the arc backwards.

## Piece (1): `roseLobeOsinPiece_isPiece`

Assume `W` is closed under `revInv` and rotation, and `X` is least area.  Write
`u = ℓ(a :: A)`, `v = ℓ(a :: (A ++ S))` and `v' = revInv ℓ(rotate m (cell j))`.  Then
`IsPiece D W ε u v` holds, witnessed by `v'`, `u' = u`, `y = z = 1`.

* `v = u ++ ℓ S` (`dartWord_append`).  `v ∈ W` because `v` is `rotate n` of the word of cell
  `i` (`dartWord_rotate`, `dartWord_cellDarts`, `rotate_mem`).
* `v' = u ++ revInv ℓ T`, because
  `revInv (ℓ T ++ revInv ℓ(a :: A)) = ℓ(a :: A) ++ revInv ℓ T`
  (`dartWord_reverse_alpha`, `revInv_append`, `revInv_revInv`).  Also `v' ∈ W` (`inv_mem`,
  `rotate_mem`).
* `|y|, |z| ≤ ε` since `|1| = 0`, and `listVal u' = 1 · listVal u · 1`.
* **Genericity.**  We need `listVal v' ≠ 1 · listVal v · 1⁻¹`, which also gives `v' ≠ v`.
  Suppose `listVal v' = listVal v`.  Cancel `listVal u` on the left to get
  `(listVal ℓ T)⁻¹ = listVal ℓ S`.  Rotate cell `j` further by `|T| + |A|` so that it reads
  `α a :: (T ++ A.reverse.map α)`.  Cell `i` reads `a :: (A ++ S)`.  The merged word
  `(A ++ S) ++ (T ++ A.reverse.map α)` then has value
  `P · s · t · P⁻¹ = P · t⁻¹ · t · P⁻¹ = 1`, where `P = listVal ℓ A`,
  `s = listVal ℓ S` and `t = listVal ℓ T`.  That contradicts
  `roseLobeOsinPiece_merge_ne_one`: cancelling the two cells would give a relator product
  with `rCellCount - 2` factors, so `X` would not be least area.

So a shared arc of two distinct cells is a piece, or `X` is not least area.  No surgery
residual remains: the surgery is `VanKampenData.exists_merge` and `planar_of_neFace`.

## Its consequence: `roseLobeOsinPiece_sharedArc_lt`

Under the cell bounds `roseLobeOsinCore_CellBounds`, the `pieces` clause applied to piece (1)
gives `|a :: A| < μ · |cell i|`.  Lengths are preserved by `dartWord` and `rotate`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- The word on a rotated dart list is the rotated word. -/
theorem roseLobeOsinPiece_dartWord_rotate {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (l : List X.toCombMap.Dart) (k : ℕ) :
    dartWord X (l.rotate k) = (dartWord X l).rotate k :=
  List.map_rotate X.label l k

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_dartWord_rotate

/-- **Piece (1): a shared arc of two distinct cells of a least-area diagram is a piece.**
Cell `i` rotated by `n` reads `a :: (A ++ S)`, and cell `j` rotated by `m` reads
`T ++ (a :: A).reverse.map α`.  Then `ℓ(a :: A)` is an `ε`-piece of `ℓ(a :: (A ++ S))`, with
the witness `revInv ℓ(rotate m (cell j))`, `y = z = 1`, and the genericity clause coming from
least area (`roseLobeOsinPiece_merge_ne_one`). -/
theorem roseLobeOsinPiece_isPiece {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} (eps : ℕ)
    (hinv : ∀ word ∈ W, HullSC.RelWord.revInv word ∈ W)
    (hrot : ∀ word ∈ W, ∀ n : ℕ, word.rotate n ∈ W)
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea) {i j : Fin X.rCellCount} (hij : i ≠ j)
    {n m : ℕ} {a : X.toCombMap.Dart} {A S T : List X.toCombMap.Dart}
    (hi : (cellDarts X i).rotate n = a :: (A ++ S))
    (hj : (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha) :
    HullSC.RelWord.IsPiece D W eps (dartWord X (a :: A)) (dartWord X (a :: (A ++ S))) := by
  -- the two face cycles through the shared edge `{a, α a}`
  have cycP : X.toCombMap.IsFaceCycle (a :: (A ++ S)) := by
    rw [← hi]
    exact (X.faceBoundary (cell X i).face).isFaceCycle.rotate n
  have haP : a ∈ (cellDarts X i).rotate n := by
    rw [hi]
    exact List.mem_cons.mpr (Or.inl rfl)
  have hPface : X.toCombMap.faceOf a = (cell X i).face :=
    ((X.faceBoundary (cell X i).face).mem_iff a).mp (List.mem_rotate.mp haP)
  have haS : X.toCombMap.alpha a ∈ (cellDarts X j).rotate m := by
    rw [hj]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨a, List.mem_reverse.mpr
      (List.mem_cons.mpr (Or.inl rfl)), rfl⟩))
  have hSface : X.toCombMap.faceOf (X.toCombMap.alpha a) = (cell X j).face :=
    ((X.faceBoundary (cell X j).face).mem_iff _).mp (List.mem_rotate.mp haS)
  have hjrot : (T ++ (a :: A).reverse.map X.toCombMap.alpha).rotate
      (T ++ A.reverse.map X.toCombMap.alpha).length =
      X.toCombMap.alpha a :: (T ++ A.reverse.map X.toCombMap.alpha) := by
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
    exact List.rotate_append_length_eq _ [X.toCombMap.alpha a]
  have cycS : X.toCombMap.IsFaceCycle
      (X.toCombMap.alpha a :: (T ++ A.reverse.map X.toCombMap.alpha)) := by
    rw [← hjrot, ← hj]
    exact ((X.faceBoundary (cell X j).face).isFaceCycle.rotate m).rotate _
  have hmerge := roseLobeOsinPiece_merge_ne_one hlea hij cycP hPface cycS hSface
  -- the words
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
  -- genericity, from least area
  have hne : RelLetter.listVal (HullSC.RelWord.revInv (dartWord X ((cellDarts X j).rotate m))) ≠
      RelLetter.listVal (dartWord X (a :: (A ++ S))) := by
    intro heq
    rw [hv'eq, hvS] at heq
    simp only [HullSC.RelWord.listVal_append] at heq
    have hst : RelLetter.listVal (HullSC.RelWord.revInv (dartWord X T)) =
        RelLetter.listVal (dartWord X S) := mul_left_cancel heq
    rw [HullSC.RelWord.listVal_revInv] at hst
    apply hmerge
    simp only [Embedded.dartWord_append, HullSC.RelWord.listVal_append,
      Embedded.dartWord_reverse_alpha, HullSC.RelWord.listVal_revInv]
    rw [← hst]
    group
  exact ⟨hvW, ⟨_, hvS⟩, _, hv'W, fun h => hne (congrArg RelLetter.listVal h), _, _, hv'eq,
    1, 1, (WordMetric.wordNorm_one _).trans_le (Nat.zero_le _),
    (WordMetric.wordNorm_one _).trans_le (Nat.zero_le _), by rw [one_mul, mul_one],
    by simpa only [one_mul, inv_one, mul_one] using hne⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_isPiece

/-- **A shared arc of two distinct cells is short.**  Under the cell bounds and least area, a
boundary arc `a :: A` shared by distinct cells `i ≠ j` (in the orientation of
`roseLobeOsinPiece_isPiece`) has fewer than `μ · |cell i|` darts. -/
theorem roseLobeOsinPiece_sharedArc_lt {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (hlea : X.LeastArea)
    {i j : Fin X.rCellCount} (hij : i ≠ j) {n m : ℕ} {a : X.toCombMap.Dart}
    {A S T : List X.toCombMap.Dart}
    (hi : (cellDarts X i).rotate n = a :: (A ++ S))
    (hj : (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha) :
    ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ) := by
  have h := hB.2.2.2.2 _ _ (roseLobeOsinPiece_isPiece eps hB.1 hB.2.1 hlea hij hi hj)
  have hu : (dartWord X (a :: A)).length = (a :: A).length := List.length_map _
  have hv : (dartWord X (a :: (A ++ S))).length = (cellDarts X i).length := by
    rw [← hi, roseLobeOsinPiece_dartWord_rotate, List.length_rotate]
    exact List.length_map _
  rw [hu, hv] at h
  exact h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_sharedArc_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
