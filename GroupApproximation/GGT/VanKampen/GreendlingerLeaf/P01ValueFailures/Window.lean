import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoinsBoundaryArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Value failures at boundary junctions: the gap windows of the outer darts

Osin (math/0411039v3, §9), proof of Lemma 9.4.  The residual
`OsinLemma94BoundaryValueFailureCountInput` (`Estimating/OsinLemma94BoundaryJunctionBudget`):
summed over the relator polygons with at least two class non-joins, the boundary value failures
number at most `n = rCellCount Δ`.

## The mathematical proof

Write `B = outerDarts Δ` (duplicate free, `y ∈ B ↔ faceOf (α y) = outer`, and consecutive
`x, y` in `B` satisfy `facePerm (α y) = α x`), and `idx y = B.idxOf y`.

**Step 0 (value failure darts).**  A value failure `s` of polygon `k` has boundary sides `s` and
`s + 1` of one kind, the last dart `e` of side `s` and the first dart `e'` of side `s + 1` lie in
`B`, `facePerm e = e'`, `faceOf e = face k ≠ outer`, the gap is
`gap e = B[idx e + 1 .. idx e')` and its word has value `≠ 1`.  Since `k` is a relator polygon,
some side of `k` is a cell side, so some dart `x` with `faceOf x = faceOf e` has `α x` on a relator
cell `C`.  Call such an `e` a *value failure dart* (`IsValueFailure`).  Distinct junctions give
distinct darts: the face of `e` recovers `k` (`face_injective`), and the sides of `k` are disjoint.

**Step 1 (the lobe).**  For a value failure dart `e`, the gap is nonempty (its value is not `1`),
so `idx e + 1 < idx e'`.  The walk `c = (gap e).reverse.map α` runs along the outer face and is
chained by face steps.  It closes by a first turn: from the last dart `α x₁` (`x₁ = B[idx e + 1]`)
rotate to `α e`, then to `facePerm e = e'`, then to `α x₂ = head c` (`x₂ = B[idx e' - 1]`).  The two
intermediate darts are off the edges of `c`: `α e`, `e'` are not in the gap by their indices, and
their reverses are not in the gap since `faceOf e = faceOf e' ≠ outer`.  So `c` bounds the face set
`lobe e = enclosedFaces c` in the successor form (`EnclosedFaceSetSucc`), with `outer ∉ lobe e`.

**Step 2 (a lobe holds a cell).**  The enclosed subdiagram `Ξ` of `lobe e` reads
`invDarts c = gap e`, with at most as many cells as `lobe e` holds.  If `lobe e` holds no cell,
`Ξ` has none, so its boundary value `listVal (gap e) = 1`, a contradiction.

**Step 3 (lobe calculus).**  (a) A gap dart off the outer face has its face in the lobe (seed).
(b) If `faceOf y ∈ lobe e` and `faceOf (α y) = outer` then `y` is on an edge of `c` (else the
enclosure propagates to `outer`).  (c) Nesting: if `e₂ ∈ gap e` is a value failure dart, then
`facePerm e₂ ∈ gap e` (by (a), (b), and `faceOf (facePerm e₂) = faceOf e₂ ≠ outer`).
(d) If neither of two distinct value failure darts lies in the gap of the other, the gaps are
disjoint (interval arithmetic on indices), and then the lobes are disjoint: the face class path
from the seed of `lobe e₁` stays inside `lobe e₁`, so it never crosses an edge of the second
walk (whose darts and reverses touch `outer`), and it links the second walk to the reversal of
its own seed, contradicting `alpha_mem_of_faceClass`.

**Step 4 (a private cell).**  For a value failure dart `e` in a set `E` of value failure darts,
pick a cell face `f ∈ lobe e` lying in the lobe of no `e₂ ∈ E ∩ gap e`.  If `E ∩ gap e = ∅`, use
Step 2.  Otherwise let `e₁ ∈ E ∩ gap e` have maximal span `idx (facePerm e₁) - idx e₁`, and let `C`
be the relator cell across a dart `x` of the face of `e₁`.  Then `f = C.face ∈ lobe e` by (a) and
two alpha steps across non-walk edges.  If `f ∈ lobe e₂` for some `e₂ ∈ E ∩ gap e`, then
`faceOf e₁ ∈ lobe e₂`, so by (b) `e₁ ∈ gap e₂`; by (c) `facePerm e₁ ∈ gap e₂`, so the span of
`e₁` is smaller than that of `e₂`, against maximality.

**Step 5 (injectivity).**  The private cell faces of distinct `e₁ ≠ e₂ ∈ E` differ: if `e₂ ∈ gap e₁`
the face of `e₁` avoids `lobe e₂`; symmetrically; otherwise the lobes are disjoint (Step 3d).  The
cell faces are faces of the list `relatorCells`, so `|E| ≤ rCellCount`.  With Step 0,
`∑ₖ |valueFailureJunctions k| = |⋃ₖ {k} × valueFailureJunctions k| ≤ rCellCount S.diagram = n`.

This module: windows of a duplicate-free list, the outer darts, the gap window, and the predicate
`IsValueFailure`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

universe u w v

/-- **Membership in a window strictly between two positions** of a duplicate-free list. -/
theorem mem_window_iff {α : Type*} [BEq α] [LawfulBEq α] {l : List α} (hnodup : l.Nodup)
    {a b : ℕ} {y : α} :
    y ∈ (l.drop (a + 1)).take (b - (a + 1)) ↔ y ∈ l ∧ a < l.idxOf y ∧ l.idxOf y < b := by
  constructor
  · intro hy
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
    have hi' : i < b - (a + 1) := by
      rw [List.length_take] at hi
      omega
    have hget : l[a + 1 + i]? = some y := by
      rw [← List.getElem?_drop, ← List.getElem?_take_of_lt hi', List.getElem?_eq_getElem hi, hiy]
    obtain ⟨hlt, hyi⟩ := List.getElem?_eq_some_iff.mp hget
    subst hyi
    refine ⟨List.getElem_mem hlt, ?_⟩
    rw [PolygonList.idxOf_getElem_of_nodup hnodup _ hlt]
    omega
  · rintro ⟨hy, hay, hyb⟩
    have hlt : l.idxOf y - (a + 1) < b - (a + 1) := by omega
    refine List.mem_iff_getElem?.mpr ⟨l.idxOf y - (a + 1), ?_⟩
    rw [List.getElem?_take_of_lt hlt, List.getElem?_drop,
      Nat.add_sub_of_le (show a + 1 ≤ l.idxOf y by omega)]
    exact List.getElem?_idxOf hy

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The position of a dart along the oriented outer darts. -/
noncomputable def idx (X : DiscDiagram.{u, w, v} W) (y : X.toCombMap.Dart) : ℕ :=
  (outerDarts X).idxOf y

/-- **The gap after a dart**: the outer darts strictly between `e` and `facePerm e`. -/
noncomputable def gap (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    List X.toCombMap.Dart :=
  ClassProducer.boundaryGapOf (outerDarts X) e (X.toCombMap.facePerm e)

theorem gap_eq (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    gap X e = ((outerDarts X).drop (idx X e + 1)).take
      (idx X (X.toCombMap.facePerm e) - (idx X e + 1)) :=
  rfl

theorem outerDarts_nodup (X : DiscDiagram.{u, w, v} W) : (outerDarts X).Nodup :=
  List.Nodup.map X.toCombMap.alpha_involutive.injective
    (List.nodup_reverse.mpr (X.faceBoundary X.outerFace).nodup)

theorem mem_outerDarts_iff (X : DiscDiagram.{u, w, v} W) (y : X.toCombMap.Dart) :
    y ∈ outerDarts X ↔ X.toCombMap.faceOf (X.toCombMap.alpha y) = X.outerFace := by
  unfold outerDarts
  exact FirstTurnWalk.mem_reverse_map_alpha_iff.trans ((X.faceBoundary X.outerFace).mem_iff _)

theorem outerDarts_isChain (X : DiscDiagram.{u, w, v} W) :
    (outerDarts X).IsChain fun x y =>
      X.toCombMap.facePerm (X.toCombMap.alpha y) = X.toCombMap.alpha x := by
  unfold outerDarts
  rw [List.isChain_map, List.isChain_reverse]
  refine (X.faceBoundary X.outerFace).chain.imp fun a b h => ?_
  show X.toCombMap.facePerm (X.toCombMap.alpha (X.toCombMap.alpha a)) =
    X.toCombMap.alpha (X.toCombMap.alpha b)
  rw [X.toCombMap.alpha_involutive a, X.toCombMap.alpha_involutive b]
  exact h

theorem outerDarts_step (X : DiscDiagram.{u, w, v} W) {i : ℕ} {x y : X.toCombMap.Dart}
    (hx : (outerDarts X)[i]? = some x) (hy : (outerDarts X)[i + 1]? = some y) :
    X.toCombMap.facePerm (X.toCombMap.alpha y) = X.toCombMap.alpha x := by
  obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hi1, hyi⟩ := List.getElem?_eq_some_iff.mp hy
  subst hxi hyi
  exact (outerDarts_isChain X).getElem i hi1

theorem facePerm_alpha (X : DiscDiagram.{u, w, v} W) (y : X.toCombMap.Dart) :
    X.toCombMap.facePerm (X.toCombMap.alpha y) = X.toCombMap.sigma y := by
  show X.toCombMap.sigma (X.toCombMap.alpha (X.toCombMap.alpha y)) = _
  rw [X.toCombMap.alpha_involutive y]

theorem idx_lt_length (X : DiscDiagram.{u, w, v} W) {y : X.toCombMap.Dart}
    (hy : y ∈ outerDarts X) : idx X y < (outerDarts X).length :=
  List.idxOf_lt_length_of_mem hy

theorem getElem?_idx (X : DiscDiagram.{u, w, v} W) {y : X.toCombMap.Dart}
    (hy : y ∈ outerDarts X) : (outerDarts X)[idx X y]? = some y :=
  List.getElem?_idxOf hy

theorem eq_of_idx_eq (X : DiscDiagram.{u, w, v} W) {x y : X.toCombMap.Dart}
    (hx : x ∈ outerDarts X) (h : idx X x = idx X y) : x = y :=
  (List.idxOf_inj hx).mp h

theorem mem_gap_iff (X : DiscDiagram.{u, w, v} W) (e y : X.toCombMap.Dart) :
    y ∈ gap X e ↔ y ∈ outerDarts X ∧ idx X e < idx X y ∧
      idx X y < idx X (X.toCombMap.facePerm e) := by
  rw [gap_eq]
  exact mem_window_iff (outerDarts_nodup X)

theorem mem_outerDarts_of_mem_gap (X : DiscDiagram.{u, w, v} W) {e y : X.toCombMap.Dart}
    (hy : y ∈ gap X e) : y ∈ outerDarts X :=
  ((mem_gap_iff X e y).mp hy).1

theorem faceOf_alpha_of_mem_gap (X : DiscDiagram.{u, w, v} W) {e y : X.toCombMap.Dart}
    (hy : y ∈ gap X e) : X.toCombMap.faceOf (X.toCombMap.alpha y) = X.outerFace :=
  (mem_outerDarts_iff X y).mp (mem_outerDarts_of_mem_gap X hy)

theorem gap_length (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart)
    (hb : idx X (X.toCombMap.facePerm e) ≤ (outerDarts X).length) :
    (gap X e).length = idx X (X.toCombMap.facePerm e) - (idx X e + 1) := by
  rw [gap_eq, List.length_take, List.length_drop]
  omega

theorem gap_getElem? (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) (t : ℕ)
    (ht : t < idx X (X.toCombMap.facePerm e) - (idx X e + 1)) :
    (gap X e)[t]? = (outerDarts X)[idx X e + 1 + t]? := by
  rw [gap_eq, List.getElem?_take_of_lt ht, List.getElem?_drop]

theorem gap_ne_nil (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hval : RelLetter.listVal (dartWord X (gap X e)) ≠ 1) : gap X e ≠ [] := by
  intro h0
  apply hval
  rw [h0]
  rfl

theorem idx_add_one_lt (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hval : RelLetter.listVal (dartWord X (gap X e)) ≠ 1) :
    idx X e + 1 < idx X (X.toCombMap.facePerm e) := by
  by_contra hle
  apply gap_ne_nil X hval
  rw [gap_eq, Nat.sub_eq_zero_of_le (by omega), List.take_zero]

/-- **A value failure dart**: an outer dart `e` off the outer face, whose face successor is an
outer dart, whose gap reads a value other than `1`, and whose face is adjacent to a relator cell. -/
def IsValueFailure (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) : Prop :=
  e ∈ outerDarts X ∧ X.toCombMap.facePerm e ∈ outerDarts X ∧
    X.toCombMap.faceOf e ≠ X.outerFace ∧
    RelLetter.listVal (dartWord X (gap X e)) ≠ 1 ∧
    ∃ x, X.toCombMap.faceOf x = X.toCombMap.faceOf e ∧
      ∃ C ∈ X.relatorCells, X.toCombMap.faceOf (X.toCombMap.alpha x) = C.face

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures
