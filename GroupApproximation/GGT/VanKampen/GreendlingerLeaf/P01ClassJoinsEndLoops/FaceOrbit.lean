import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoins
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCovers
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassProducerGaps
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCycle
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.Estimating.QuasiGeodesicValueOneGap
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.GGT.VanKampen.Estimating.RegionPartition
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: face walks

Target (in `Proof.lean`): `OsinLemma94ClassJoinsEndLoopsInput`.  This module collects the face-walk
helpers.  The whole route is recorded here.

## Notation

`X = S.diagram`, `M` its map, `f = facePerm = σ α`, `Π = (cell i).face`, `n = |cellDarts i|`,
`L₀ = ⌈c / λ⌉₊`.  Take `ε₀ = 0`, `B = (2ε + 2) L₀` and `ρ₀ = max ρ₁ (2 L₀ + 3)`, with `ρ₁` from
the same-cell pocket value input, so `n ≥ ρ > 2 L₀ + 2`.  The walk `seg x l` is
`x, f x, …, f^(l-1) x`, and `back q L` is the list `α (f⁻¹ q), …, α (f^(-L) q)`.

## The lists

* `classEnd k i _ = back (α e) L₀` for the last dart `e` of the class `(k, i)` (nothing if the
  class is empty), of length `≤ L₀ ≤ B`.
* `regionEnd a _ = flatMap (fun z => back (α z) L₀)` over the right and left sides of `a` and the
  reverses of the first darts of both arcs, of length `≤ (2ε + 2) L₀ = B`.

## Pockets

A *pocket* of cell `i` is a walk `seg x ℓ` on `cellDarts i` with `ℓ ≤ n`, value one, and
`σ.SameCycle x (f^ℓ x)` (its two ends at one vertex).  By the quasi-geodesic cell words,
`ℓ ≤ L₀`.  For the unbound dart `d` of clause (c), `α d` lies on a relator side of a
single-class polygon `k` whose class is a reversed arc of cell `i` (the faces force the cell).
The class closes up: the value of the class word is the corner value `1`, and the last dart `α y`
of the class meets its first dart `α (f^(ℓ-1) y)` by `σ`, so the arc `seg y ℓ` is a pocket
through `d`.  Let `J ≤ L₀` be the largest length of a pocket through `d`, with base `x`,
`d = f^s x`, `s < J`, and put `p = f^J x`, `u = f^(J-1) x`.

## Separation

In the map `joined u w` (`w = f^(n-1) x`), `not_reach` separates `f u = p` from `f w = x`: the two
darts differ, lie on one face, and `σ (α u) = p`, `σ (α w) = x` lie at one vertex.  Walking
backwards, `x, f x, …, f^(J-1) x` are all apart from `p`, and so are their reverses.  Darts on
faces other than `Π` reach every dart of their face.

## Cases on `p`

1. `faceOf (α p) = Π`, `α p = f^q x`.  `q < J` contradicts the separation; `q = J` is `α p = p`.
   For `q > J` either `p` or `α p` is oriented; the same-cell pocket value gives a pocket
   `seg x (q + 1)` or `seg (α p) (n - q + J + 1)` through `d`, longer than `J`.
2. `p` on an arc of a region `a` at cell `i`, `p = f^r st` with `st` the first dart of the arc.
   If `r ≥ J - s` then `d` is on the arc, so `d` is bound.  Otherwise `f^(J-s-r) d = st`, so
   `α d ∈ back (α (α st)) L₀ ⊆ regionEnd a`.
3. `p` unbound and `faceOf (α p) ≠ Π`.  If `faceOf (α p)` is in a region `a`, then `Π ∉ a`, so
   `α p` is on the boundary of `a`: on the source reversal (so `p` bound), on a side (so
   `α d ∈ back p L₀ ⊆ regionEnd a`) or on the target (outer, impossible; or `p` bound).
   Otherwise `α p` is on a relator side of a polygon `k'` (with cell `i`), in a class `i'`
   whose darts are a reversed arc `seg y ℓ'`, `p = f^t y`.
   * `t = 0`: `α p` is the last class dart, so `α d ∈ classEnd k' i'`.  If `k'` has at least two
     classes it is a budget polygon; if one, the class is a pocket through `p` and
     `seg x J ++ seg p ℓ'` is a pocket through `d`, longer than `J`.
   * `t ≥ 1`: `α u` is the next class dart.  On a side it is on the face of `k'`, which reaches
     `p`: impossible.  In a gap `cellGapOf (α e') (α e)`, `u = f^(τ+1) (α e')` and `α e'` reaches
     `p`, so `α e' = f^q x` with `q ≥ J`; the gap then contains all of `α (f^j x)`, `j < J`, and
     `α d` is a class dart of `(k', i')`.  With two classes this is option 1; with one class the
     class is a pocket containing `seg x J` and `p`, through `d`, longer than `J`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

/-- The face walk of length `l` from `x`. -/
def seg (M : CombMap.{v}) (x : M.Dart) (l : ℕ) : List M.Dart :=
  (List.range l).map fun t => (M.facePerm ^ t) x

/-- The reverses of the `L` face predecessors of `q`, nearest first. -/
def back (M : CombMap.{v}) (q : M.Dart) (L : ℕ) : List M.Dart :=
  (List.range L).map fun t => M.alpha ((M.facePerm ^ (t + 1)).symm q)

section Orbit

variable {M : CombMap.{v}}

theorem length_seg (x : M.Dart) (l : ℕ) : (seg M x l).length = l := by
  simp only [seg, List.length_map, List.length_range]

theorem length_back (q : M.Dart) (L : ℕ) : (back M q L).length = L := by
  simp only [back, List.length_map, List.length_range]

theorem getElem_seg (x : M.Dart) {l t : ℕ} (h : t < (seg M x l).length) :
    (seg M x l)[t] = (M.facePerm ^ t) x := by
  simp only [seg, List.getElem_map, List.getElem_range]

theorem mem_seg_iff {x y : M.Dart} {l : ℕ} :
    y ∈ seg M x l ↔ ∃ t < l, (M.facePerm ^ t) x = y := by
  simp only [seg, List.mem_map, List.mem_range]

theorem pow_mem_seg (x : M.Dart) {l t : ℕ} (ht : t < l) : (M.facePerm ^ t) x ∈ seg M x l :=
  mem_seg_iff.mpr ⟨t, ht, rfl⟩

theorem seg_add (x : M.Dart) (a b : ℕ) :
    seg M x (a + b) = seg M x a ++ seg M ((M.facePerm ^ a) x) b := by
  simp only [seg, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [add_comm a t, pow_add, Equiv.Perm.mul_apply]

theorem seg_succ (x : M.Dart) (a : ℕ) :
    seg M x (a + 1) = seg M x a ++ [(M.facePerm ^ a) x] := by
  rw [seg_add]
  simp only [seg, List.range_one, List.map_cons, List.map_nil, pow_zero, Equiv.Perm.one_apply]

theorem seg_succ' (x : M.Dart) (a : ℕ) :
    seg M x (a + 1) = x :: seg M (M.facePerm x) a := by
  rw [add_comm, seg_add]
  simp only [seg, List.range_one, List.map_cons, List.map_nil, pow_zero, Equiv.Perm.one_apply,
    pow_one, List.cons_append, List.nil_append]

theorem mem_back {z q : M.Dart} {t L : ℕ} (h : (M.facePerm ^ (t + 1)) z = q) (ht : t < L) :
    M.alpha z ∈ back M q L := by
  refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
  show M.alpha ((M.facePerm ^ (t + 1)).symm q) = M.alpha z
  rw [← h, Equiv.symm_apply_apply]

/-- Cancelling common face steps. -/
theorem pow_shift {x y : M.Dart} {a b t : ℕ}
    (h : (M.facePerm ^ (a + t)) y = (M.facePerm ^ (b + t)) x) :
    (M.facePerm ^ a) y = (M.facePerm ^ b) x := by
  rw [add_comm a t, add_comm b t, pow_add, pow_add, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply] at h
  exact (M.facePerm ^ t).injective h

theorem pow_apply_add (x : M.Dart) (a b : ℕ) :
    (M.facePerm ^ (a + b)) x = (M.facePerm ^ a) ((M.facePerm ^ b) x) := by
  rw [pow_add, Equiv.Perm.mul_apply]

theorem faceOf_pow (x : M.Dart) (t : ℕ) : M.faceOf ((M.facePerm ^ t) x) = M.faceOf x :=
  JunctionPocket.faceOf_pow_apply x t

/-- Every dart of a list of face walks sits on the face of the base. -/
theorem faceOf_of_mem_seg {x y : M.Dart} {l : ℕ} (hy : y ∈ seg M x l) :
    M.faceOf y = M.faceOf x := by
  obtain ⟨t, _, rfl⟩ := mem_seg_iff.mp hy
  exact faceOf_pow x t

/-- The length of a flatMap with bounded pieces. -/
theorem length_flatMap_le {α β : Type*} {g : α → List β} {L : ℕ} :
    ∀ {l : List α}, (∀ x ∈ l, (g x).length ≤ L) → (l.flatMap g).length ≤ l.length * L
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_one_mul]
    have h1 := h x List.mem_cons_self
    have h2 := length_flatMap_le (g := g) (l := l) fun y hy => h y (List.mem_cons_of_mem x hy)
    omega

/-- The head and the last entry of a rotated range close up cyclically. -/
theorem rotate_range_head_last {N base s0 sl : ℕ} (hN : 0 < N)
    (h0 : ((List.range N).rotate base).head? = some s0)
    (hl : ((List.range N).rotate base).getLast? = some sl) : (sl + 1) % N = s0 := by
  rw [List.head?_eq_getElem?, List.getElem?_rotate (l := List.range N) (m := 0) (n := base)
    (by rw [List.length_range]; exact hN), List.length_range,
    List.getElem?_range (Nat.mod_lt _ hN), Option.some.injEq] at h0
  rw [List.getLast?_eq_getElem?, List.length_rotate, List.length_range,
    List.getElem?_rotate (l := List.range N) (m := N - 1) (n := base)
      (by rw [List.length_range]; omega), List.length_range,
    List.getElem?_range (Nat.mod_lt _ hN), Option.some.injEq] at hl
  rw [← h0, ← hl, Nat.mod_add_mod, show N - 1 + base + 1 = base + N by omega,
    Nat.add_mod_right, Nat.zero_add]

/-- The darts of a same-cell junction gap. -/
theorem mem_cellGapOf {a b z : M.Dart} (h : ∃ m, (M.facePerm ^ (m + 1)) a = b) :
    z ∈ ClassProducer.cellGapOf M a b ↔
      ∃ t < Nat.find h, M.alpha ((M.facePerm ^ (t + 1)) a) = z := by
  rw [ClassProducer.cellGapOf, dif_pos h]
  simp only [List.mem_reverse, List.mem_map, List.mem_range]

end Orbit

section Cell

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}

theorem pow_length_cell {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i) :
    (X.toCombMap.facePerm ^ (cellDarts X i).length) z = z := by
  have hz' : z ∈ (X.faceBoundary (cell X i).face).darts := hz
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz'
  exact OsinUnboundSameCellCycle.pow_length _ hk

theorem pow_inj_cell {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i) {a b : ℕ}
    (ha : a < (cellDarts X i).length) (hb : b < (cellDarts X i).length)
    (h : (X.toCombMap.facePerm ^ a) z = (X.toCombMap.facePerm ^ b) z) : a = b := by
  have hz' : z ∈ (X.faceBoundary (cell X i).face).darts := hz
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz'
  exact OsinUnboundSameCellCycle.pow_inj _ hk ha hb h

theorem pow_mem_cell {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i) (j : ℕ) :
    (X.toCombMap.facePerm ^ j) z ∈ cellDarts X i := by
  have hz' : z ∈ (X.faceBoundary (cell X i).face).darts := hz
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz'
  exact OsinUnboundSameCellCycle.mem_of_pow _ hk j

theorem exists_pow_cell {z y : X.toCombMap.Dart} (hz : z ∈ cellDarts X i)
    (hy : y ∈ cellDarts X i) :
    ∃ j < (cellDarts X i).length, (X.toCombMap.facePerm ^ j) z = y := by
  have hz' : z ∈ (X.faceBoundary (cell X i).face).darts := hz
  have hy' : y ∈ (X.faceBoundary (cell X i).face).darts := hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz'
  exact OsinUnboundSameCellCycle.exists_pow_eq _ hk hy'

theorem mem_cell_of_faceOf {z : X.toCombMap.Dart} (hz : X.toCombMap.faceOf z = (cell X i).face) :
    z ∈ cellDarts X i :=
  ((X.faceBoundary (cell X i).face).mem_iff z).mpr hz

theorem pow_add_length_cell {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i) (a : ℕ) :
    (X.toCombMap.facePerm ^ (a + (cellDarts X i).length)) z = (X.toCombMap.facePerm ^ a) z := by
  rw [pow_add, Equiv.Perm.mul_apply, pow_length_cell hz]

theorem pow_mod_cell {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i) (a : ℕ) :
    (X.toCombMap.facePerm ^ a) z =
      (X.toCombMap.facePerm ^ (a % (cellDarts X i).length)) z := by
  conv_lhs => rw [← Nat.mod_add_div a (cellDarts X i).length]
  rw [pow_add, Equiv.Perm.mul_apply, pow_mul,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (pow_length_cell hz)]

/-- A face walk of at most `n` darts on a cell is an arc of the cell. -/
theorem exists_arc_seg {x : X.toCombMap.Dart} (hx : x ∈ cellDarts X i) {l : ℕ}
    (hl : l ≤ (cellDarts X i).length) :
    ∃ A : CyclicArc (cellDarts X i), A.darts = seg X.toCombMap x l := by
  have hx' : x ∈ (X.faceBoundary (cell X i).face).darts := hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx'
  refine ⟨⟨⟨k, Nat.lt_succ_of_lt hk⟩, l, hl⟩, List.ext_getElem ?_ fun t h1 _ => ?_⟩
  · rw [CyclicArc.darts_length, length_seg]
  · rw [OsinUnboundSameCellCycle.getElem_darts (cycle := cellDarts X i)
      (X.faceBoundary (cell X i).face) rfl _ h1, getElem_seg]
    simp only [Nat.mod_eq_of_lt hk]

/-- An arc of a cell is a face walk from a dart of the cell. -/
theorem arc_seg {cycle : List X.toCombMap.Dart} (hcyc : cycle = cellDarts X i)
    (A : CyclicArc cycle) : ∃ y ∈ cellDarts X i, A.darts = seg X.toCombMap y A.length := by
  subst hcyc
  have hpos : 0 < (X.faceBoundary (cell X i).face).darts.length :=
    List.length_pos_iff.mpr (X.faceBoundary (cell X i).face).nonempty
  refine ⟨(X.faceBoundary (cell X i).face).darts[A.start.1 %
      (X.faceBoundary (cell X i).face).darts.length]'(Nat.mod_lt _ hpos), List.getElem_mem _,
    List.ext_getElem ?_ fun t h1 _ => ?_⟩
  · rw [CyclicArc.darts_length, length_seg]
  · rw [OsinUnboundSameCellCycle.getElem_darts (cycle := cellDarts X i)
      (X.faceBoundary (cell X i).face) rfl A h1, getElem_seg]

/-- A value-one walk of at most `n` darts on a cell has at most `⌈c / λ⌉₊` darts. -/
theorem pocket_len_le {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    {x : X.toCombMap.Dart} (hx : x ∈ cellDarts X i) {l : ℕ}
    (hl : l ≤ (cellDarts X i).length)
    (hval : RelLetter.listVal (dartWord X (seg X.toCombMap x l)) = 1) :
    l ≤ ⌈c / lambda⌉₊ := by
  obtain ⟨A, hA⟩ := exists_arc_seg hx hl
  have hq := CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hW A
  rw [hA] at hq
  have hlen : (dartWord X (seg X.toCombMap x l)).length = l := by
    simp only [dartWord, List.length_map, length_seg]
  refine IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one hq hlambda (i := 0) (m := l)
    (by rw [hlen, Nat.zero_add]) ?_
  have htake : (dartWord X (seg X.toCombMap x l)).take l = dartWord X (seg X.toCombMap x l) :=
    List.take_of_length_le (le_of_eq hlen)
  rw [List.drop_zero, htake]
  exact hval

/-- A reversed dart on the target side of a region. -/
theorem alpha_mem_targetBoundaryDarts :
    ∀ (target : Option (Fin X.rCellCount)) (arc : CyclicArc (targetDarts X target))
      (p : X.toCombMap.Dart), X.toCombMap.alpha p ∈ targetBoundaryDarts X target arc →
      X.toCombMap.faceOf p = X.outerFace ∨
        ∃ j, target = some j ∧ p ∈ arc.darts ∧ X.toCombMap.faceOf p = (cell X j).face
  | none, arc, p, h => by
    left
    have hc : X.toCombMap.alpha p ∈ outerDarts X := arc.mem_cycle_of_mem_darts h
    have hc' : X.toCombMap.alpha p ∈
        (X.faceBoundary X.outerFace).darts.reverse.map X.toCombMap.alpha := hc
    obtain ⟨z, hz, hzp⟩ := List.mem_map.mp hc'
    rw [X.toCombMap.alpha.injective hzp] at hz
    exact ((X.faceBoundary X.outerFace).mem_iff p).mp (List.mem_reverse.mp hz)
  | some j, arc, p, h => by
    right
    have h' : X.toCombMap.alpha p ∈ arc.darts.reverse.map X.toCombMap.alpha := h
    obtain ⟨z, hz, hzp⟩ := List.mem_map.mp h'
    rw [X.toCombMap.alpha.injective hzp] at hz
    have hp : p ∈ arc.darts := List.mem_reverse.mp hz
    exact ⟨j, rfl, hp, faceOf_of_mem_cellDarts (i := j) (arc.mem_cycle_of_mem_darts hp)⟩

/-- A reversed dart on the source side of a region. -/
theorem mem_of_alpha_mem_reverseDarts {cycle : List X.toCombMap.Dart} (A : CyclicArc cycle)
    {p : X.toCombMap.Dart} (h : X.toCombMap.alpha p ∈ A.reverseDarts) : p ∈ A.darts := by
  have h' : X.toCombMap.alpha p ∈ A.darts.reverse.map X.toCombMap.alpha := h
  obtain ⟨z, hz, hzp⟩ := List.mem_map.mp h'
  rw [X.toCombMap.alpha.injective hzp] at hz
  exact List.mem_reverse.mp hz

end Cell

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.back
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.length_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.length_back
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.getElem_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_seg_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_mem_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.seg_add
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.seg_succ
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.seg_succ'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_back
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_shift
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_apply_add
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.faceOf_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.faceOf_of_mem_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.length_flatMap_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.rotate_range_head_last
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_cellGapOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_length_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_inj_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_mem_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.exists_pow_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_cell_of_faceOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_add_length_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pow_mod_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.exists_arc_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.arc_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.pocket_len_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.alpha_mem_targetBoundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_of_alpha_mem_reverseDarts
