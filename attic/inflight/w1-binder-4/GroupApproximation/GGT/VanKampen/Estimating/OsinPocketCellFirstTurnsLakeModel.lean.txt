import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkFollowsModel
import GroupApproximation.Meta.AxiomGuard

/-!
# First-turn order of a pocket: model tests on lakes and the double touch

A model test for item (a) of the open list for `CellPocketPinchSectionInput`
(`Estimating/OsinPocketCellPinchSection.lean`): produce first-turn order
(`CellPocketFaceSet.FirstTurns`, `Estimating/OsinPocketCellPinchFirstTurn.lean`) for the cell pocket
in walk order given by `exists_cellPocketFaceSet_closedWalk_of_orient`.  That pocket has the side
of its walk as faces and the walk as boundary cycle.

First-turn order is complement-side following.  For each dart `d` of the boundary cycle and the
next dart `e`, rotating from `e` must reach `alpha d` before any other dart on an edge of the cycle.
hull-select's `FirstTurnWalk.outerCycle_followsBoundary` derives the following of the outer cycle
from it.  A first turn onto an edge of the cycle is unique (`FirstTurn.eq_of_walkKeep`).  So the list
is one orbit of the first-turn predecessor, and a lake, which splits that predecessor into several
orbits, leaves no ordering of the boundary cycle in first-turn order.

* `FirstTurnOrder M p hne`: the chain condition of `CellPocketFaceSet.FirstTurns` on a list `p`
  (`CellPocketFaceSet.firstTurns_iff_firstTurnOrder`, by `Iff.rfl`).
* `FirstTurn.eq_of_walkKeep`, `FirstTurn.eq_sigma_alpha_of_walkKeep`: uniqueness of first turns
  onto the edges of the walk.
* `FirstTurnOrder.not_of_sigma_eq_alpha`: a dart whose rotation is its own reversal (a monogon
  across it) blocks first-turn order.
* `FirstTurnOrder.all_or_none`: a set of darts of the cycle closed under first-turn predecessors
  holds all darts of the cycle or none.
* `CellPocketFaceSet.not_firstTurns_of_sigma_eq_alpha`, `CellPocketFaceSet.firstTurns_all_or_none`:
  the same for cell pockets.
* Calibration on landed maps with monogon cells, both with full arcs.
  - The multiple-edge lake of `OsinPocketMultipleEdgeLakeModel` has the pocket `[0,2,5]` and the
    monogon `Πᵢ = [1]`.
  - The double touch of `OsinPocketCellWalkFollowsModel` has the walk `[0,2,4,6]`.
  - On both, no list holding the monogon dart and another dart is in first-turn order
    (`multipleEdgeLake_not_firstTurnOrder`, `doubleTouch_not_firstTurnOrder`).
* A lake with proper arcs and no monogon (`OsinPocketCellFirstTurnsLakeModel.M`).
  - The map has fourteen darts, four vertices (`v`, `w`, `x`, `y`) and seven edges.
  - Faces: the pocket `K = [0,2,4,8,10]`, the cell `Πᵢ = [3,6]`, a G-face `H = [1,5,7]`, the cell
    `Πⱼ = [11,12]` and the exterior `[9,13]`.
  - The lake `{Πᵢ, H}` of `K` meets the rest of the complement only at `v`.
  - The walk reads the side `[0]`, the reversed proper arc `[3]` of `Πᵢ`, the side `[4,8]` and the
    reversed proper arc `[11]` of `Πⱼ` (`properArcs`).
  - It is noncrossing and not simple (`planar`, `isNoncrossingClosedWalk_walk`,
    `walk_not_isSimpleClosedWalk`).
  - Its first-turn predecessors cycle `{0, 2, 4}` around the lake and `{8, 10}` around the exterior,
    so no list holding `0`, `2`, `4` and `8` inside the walk darts is in first-turn order
    (`properLake_not_firstTurnOrder`).

So item (a) as stated fails at map level on a lake with proper arcs and no monogon: no boundary cycle
of the side of the walk is in first-turn order, whatever its ordering.  A producer of first-turn order
has to change the diagram or the face set, or rule the lake out from least area and the optimal
family.  The models carry no labels, relator words, regions or least-area data.  Whether a least-area
diagram with letter labels carries such a pocket is not decided here.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u w v

/-- **A list in first-turn order**: the chain condition of `CellPocketFaceSet.FirstTurns` on the
list `p`.  For each dart `d` and the next dart `e`, and for the last dart and the first, rotating
from `e` reaches `alpha d` past darts off the edges of `p`. -/
def FirstTurnOrder (M : CombMap.{u}) (p : List M.Dart) (hne : p ≠ []) : Prop :=
  p.IsChain (fun d e => FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d)) ∧
    FirstTurn M (p.reverse.map M.alpha) (M.alpha (p.head hne)) (M.alpha (p.getLast hne))

namespace FirstTurn

variable {M : CombMap.{u}} {c : List M.Dart} {x y y' : M.Dart}

/-- **A first turn onto an edge of `c` is unique.** -/
theorem eq_of_walkKeep (h : FirstTurn M c x y) (h' : FirstTurn M c x y')
    (hy : walkKeep M c y) (hy' : walkKeep M c y') : y = y' := by
  obtain ⟨k, hk, rfl, havoid⟩ := h
  obtain ⟨k', hk', rfl, havoid'⟩ := h'
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · exact (havoid' k hk hlt hy).elim
  · rfl
  · exact (havoid k' hk' hgt hy').elim

/-- **A first turn whose first rotation step meets an edge of `c` is that step.** -/
theorem eq_sigma_alpha_of_walkKeep (h : FirstTurn M c x y)
    (hkeep : walkKeep M c (M.sigma (M.alpha x))) : M.sigma (M.alpha x) = y := by
  obtain ⟨k, hk, rfl, havoid⟩ := h
  rcases Nat.lt_or_ge 1 k with h1 | h1
  · exact (havoid 1 Nat.one_pos h1 (by rwa [pow_one])).elim
  · obtain rfl : k = 1 := by omega
    rw [pow_one]

end FirstTurn

namespace FirstTurnOrder

variable {M : CombMap.{u}} {p : List M.Dart} {hne : p ≠ []}

/-- The reversal of a dart of `p` lies on an edge of the reversed walk. -/
theorem walkKeep_reverse_map_alpha_of_mem {d : M.Dart} (hd : d ∈ p) :
    walkKeep M (p.reverse.map M.alpha) (M.alpha d) := by
  show M.alpha d ∈ p.reverse.map M.alpha ∨ M.alpha (M.alpha d) ∈ p.reverse.map M.alpha
  exact Or.inl (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)

/-- **The first-turn predecessor among the darts of `p` is unique.** -/
theorem pred_eq_of_firstTurn {d e z : M.Dart}
    (h : FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d)) (hd : d ∈ p)
    (hz' : FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha z)) (hz : z ∈ p) : d = z :=
  M.alpha.injective (h.eq_of_walkKeep hz' (walkKeep_reverse_map_alpha_of_mem hd)
    (walkKeep_reverse_map_alpha_of_mem hz))

/-- **The first-turn predecessor is determined when the rotation meets the walk at once.**  If the
rotation of `e` is the reversal of a dart `z` of `p`, then the only dart `d` with a first turn from
`alpha e` to `alpha d` along the reversed walk is `z`. -/
theorem pred_eq_of_sigma_mem {d e z : M.Dart}
    (h : FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d)) (hz : z ∈ p)
    (hσ : M.sigma e = M.alpha z) : d = z := by
  have hae : M.alpha (M.alpha e) = e := M.alpha_involutive e
  have hkeep : walkKeep M (p.reverse.map M.alpha) (M.sigma (M.alpha (M.alpha e))) := by
    rw [hae, hσ]
    exact walkKeep_reverse_map_alpha_of_mem hz
  have heq := h.eq_sigma_alpha_of_walkKeep hkeep
  rw [hae, hσ] at heq
  exact (M.alpha.injective heq).symm

/-- **A predecessor other than itself.**  In a duplicate-free list in first-turn order, a dart beside
which the list holds another dart has a first-turn predecessor other than itself. -/
theorem exists_pred (hp : FirstTurnOrder M p hne) (hnodup : p.Nodup) {e b : M.Dart}
    (he : e ∈ p) (hb : b ∈ p) (heb : e ≠ b) :
    ∃ d ∈ p, d ≠ e ∧ FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d) :=
  PinchFirstTurn.exists_mem_ne_rel_of_isChain
    (R := fun d e => FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d))
    hne hnodup hp.1 hp.2 he hb heb

/-- **A monogon across a dart blocks first-turn order.**  If the rotation of a dart `e` of a
duplicate-free list is its own reversal, and the list holds another dart, then the list is not in
first-turn order: the first-turn predecessor of `e` would be `e` itself. -/
theorem not_of_sigma_eq_alpha (hnodup : p.Nodup) {e b : M.Dart} (he : e ∈ p) (hb : b ∈ p)
    (heb : e ≠ b) (hσ : M.sigma e = M.alpha e) : ¬ FirstTurnOrder M p hne := by
  intro hp
  obtain ⟨d, -, hde, hturn⟩ := hp.exists_pred hnodup he hb heb
  exact hde (pred_eq_of_sigma_mem hturn he hσ)

/-- **A set closed under first-turn predecessors holds all darts or none.**  Split on the first dart:
if it lies in the set, the closing turn puts the last dart in the set, and backwards induction along
the chain gives every dart; otherwise induction along the chain keeps every dart out. -/
theorem all_or_none (hp : FirstTurnOrder M p hne) (S : M.Dart → Prop)
    (hS : ∀ ⦃d e : M.Dart⦄, d ∈ p → e ∈ p →
      FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d) → S e → S d) :
    (∀ x ∈ p, S x) ∨ ∀ x ∈ p, ¬ S x := by
  have hchain : p.IsChain (fun d e => d ∈ p ∧ e ∈ p ∧
      FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d)) :=
    hp.1.imp_of_mem_imp fun _ _ hd he h => ⟨hd, he, h⟩
  by_cases hhead : S (p.head hne)
  · exact Or.inl (List.IsChain.backwards_induction S p hchain
      (fun _ _ h hy => hS h.1 h.2.1 h.2.2 hy)
      (fun _ => hS (List.getLast_mem hne) (List.head_mem hne) hp.2 hhead))
  · exact Or.inr (List.IsChain.induction (fun x => ¬ S x) p hchain
      (fun _ _ h hx hy => hx (hS h.1 h.2.1 h.2.2 hy)) (fun _ => hhead))

end FirstTurnOrder

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **First-turn order of a cell pocket is first-turn order of its boundary cycle.** -/
theorem firstTurns_iff_firstTurnOrder (K : CellPocketFaceSet D eps X i j) :
    K.FirstTurns ↔ FirstTurnOrder X.toCombMap K.boundary.cycle K.boundary.cycle_nonempty :=
  Iff.rfl

/-- **A monogon across a boundary dart blocks first-turn order of a cell pocket.** -/
theorem not_firstTurns_of_sigma_eq_alpha (K : CellPocketFaceSet D eps X i j)
    {e b : X.toCombMap.Dart} (he : e ∈ K.boundary.cycle) (hb : b ∈ K.boundary.cycle) (heb : e ≠ b)
    (hσ : X.toCombMap.sigma e = X.toCombMap.alpha e) : ¬ K.FirstTurns :=
  FirstTurnOrder.not_of_sigma_eq_alpha K.boundary.cycle_nodup he hb heb hσ

/-- **In a cell pocket in first-turn order, a set closed under first-turn predecessors holds every
boundary dart or none.** -/
theorem firstTurns_all_or_none (K : CellPocketFaceSet D eps X i j) (hK : K.FirstTurns)
    (S : X.toCombMap.Dart → Prop)
    (hS : ∀ ⦃d e : X.toCombMap.Dart⦄, d ∈ K.boundary.cycle → e ∈ K.boundary.cycle →
      FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
        (X.toCombMap.alpha e) (X.toCombMap.alpha d) → S e → S d) :
    (∀ x ∈ K.boundary.cycle, S x) ∨ ∀ x ∈ K.boundary.cycle, ¬ S x :=
  FirstTurnOrder.all_or_none hK S hS

end CellPocketFaceSet

namespace OsinPocketCellFirstTurnsLakeModel

/-- **The multiple-edge lake admits no first-turn order.**  The pocket walk dart `0` bounds the
monogon lake `Πᵢ = [1]`, so its rotation is its own reversal. -/
theorem multipleEdgeLake_not_firstTurnOrder (p : List OsinPocketMultipleEdgeLakeModel.M.Dart)
    (hne : p ≠ []) (hnodup : p.Nodup) (h0 : (0 : OsinPocketMultipleEdgeLakeModel.M.Dart) ∈ p)
    (h2 : (2 : OsinPocketMultipleEdgeLakeModel.M.Dart) ∈ p) :
    ¬ FirstTurnOrder OsinPocketMultipleEdgeLakeModel.M p hne :=
  FirstTurnOrder.not_of_sigma_eq_alpha hnodup h0 h2 (by decide) (by decide)

/-- The pocket walk `[0,2,5]` of the multiple-edge lake is not in first-turn order. -/
theorem multipleEdgeLake_pocketCycle_not_firstTurnOrder :
    ¬ FirstTurnOrder OsinPocketMultipleEdgeLakeModel.M
      ([0, 2, 5] : List OsinPocketMultipleEdgeLakeModel.M.Dart) (List.cons_ne_nil _ _) :=
  multipleEdgeLake_not_firstTurnOrder _ _ (by decide) (by decide) (by decide)

/-- **The double touch admits no first-turn order.**  The walk dart `4` bounds the monogon `[5]`
off the side of the walk, so its rotation is its own reversal. -/
theorem doubleTouch_not_firstTurnOrder (p : List OsinPocketCellWalkFollowsModel.M.Dart)
    (hne : p ≠ []) (hnodup : p.Nodup) (h4 : (4 : OsinPocketCellWalkFollowsModel.M.Dart) ∈ p)
    (h0 : (0 : OsinPocketCellWalkFollowsModel.M.Dart) ∈ p) :
    ¬ FirstTurnOrder OsinPocketCellWalkFollowsModel.M p hne :=
  FirstTurnOrder.not_of_sigma_eq_alpha hnodup h4 h0 (by decide) (by decide)

/-- The walk `[0,2,4,6]` of the double touch is not in first-turn order. -/
theorem doubleTouch_walk_not_firstTurnOrder :
    ¬ FirstTurnOrder OsinPocketCellWalkFollowsModel.M
      ([0, 2, 4, 6] : List OsinPocketCellWalkFollowsModel.M.Dart) (List.cons_ne_nil _ _) :=
  doubleTouch_not_firstTurnOrder _ _ (by decide) (by decide) (by decide)

def properAlpha : Perm (Fin 14) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  left_inv := by decide
  right_inv := by decide

def properSigma : Perm (Fin 14) where
  toFun := ![5, 2, 6, 4, 7, 8, 1, 3, 13, 10, 12, 0, 9, 11]
  invFun := ![11, 6, 1, 7, 3, 0, 2, 4, 5, 12, 9, 13, 10, 8]
  left_inv := by decide
  right_inv := by decide

/-- **A lake with proper arcs.**  Four vertices: `v` with rotation `0 ↦ 5 ↦ 8 ↦ 13 ↦ 11 ↦ 0`,
`w` with `1 ↦ 2 ↦ 6 ↦ 1`, `x` with `3 ↦ 4 ↦ 7 ↦ 3` and `y` with `9 ↦ 10 ↦ 12 ↦ 9`.  The edges are
`{0,1}` from `v` to `w`, `{2,3}` and `{6,7}` from `w` to `x`, `{4,5}` from `x` to `v`, and `{8,9}`,
`{10,11}` and `{12,13}` between `v` and `y`. -/
def M : CombMap where
  Dart := Fin 14
  dartFintype := inferInstance
  alpha := properAlpha
  sigma := properSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 14))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 14) n)

def faceClass : Fin 14 → Fin 5 := ![0, 2, 0, 1, 0, 2, 1, 2, 0, 4, 0, 3, 3, 4]
def faceRep : Fin 5 → Fin 14 := ![0, 3, 1, 11, 9]

noncomputable def faceEquiv : M.Face ≃ Fin 5 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 1, 2, 2, 0, 1, 2, 0, 3, 3, 0, 3, 0] : Fin 14 → Fin 4)
    (![0, 1, 3, 9] : Fin 4 → Fin 14) (by decide) (by decide) (by decide)

/-- The map is planar, with four vertices, seven edges and five faces. -/
theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 14, Relation.EqvGen M.Adjacent 0 d := by
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inr rfl)
      have h58 : Relation.EqvGen M.Adjacent 5 8 := .rel _ _ (Or.inr rfl)
      have h813 : Relation.EqvGen M.Adjacent 8 13 := .rel _ _ (Or.inr rfl)
      have h1311 : Relation.EqvGen M.Adjacent 13 11 := .rel _ _ (Or.inr rfl)
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h26 : Relation.EqvGen M.Adjacent 2 6 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h54 : Relation.EqvGen M.Adjacent 5 4 := .rel _ _ (Or.inl rfl)
      have h47 : Relation.EqvGen M.Adjacent 4 7 := .rel _ _ (Or.inr rfl)
      have h89 : Relation.EqvGen M.Adjacent 8 9 := .rel _ _ (Or.inl rfl)
      have h1110 : Relation.EqvGen M.Adjacent 11 10 := .rel _ _ (Or.inl rfl)
      have h1312 : Relation.EqvGen M.Adjacent 13 12 := .rel _ _ (Or.inl rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 := .trans _ _ _ h01 h12
      have h04 : Relation.EqvGen M.Adjacent 0 4 := .trans _ _ _ h05 h54
      have h08 : Relation.EqvGen M.Adjacent 0 8 := .trans _ _ _ h05 h58
      have h013 : Relation.EqvGen M.Adjacent 0 13 := .trans _ _ _ h08 h813
      have h011 : Relation.EqvGen M.Adjacent 0 11 := .trans _ _ _ h013 h1311
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact .trans _ _ _ h02 h23
      · exact h04
      · exact h05
      · exact .trans _ _ _ h02 h26
      · exact .trans _ _ _ h04 h47
      · exact h08
      · exact .trans _ _ _ h08 h89
      · exact .trans _ _ _ h011 h1110
      · exact h011
      · exact .trans _ _ _ h013 h1312
      · exact h013
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 4 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 5 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 14 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 7 := by omega
    rw [heq]
    norm_num

/-- One rotation step from the reversal of each walk dart reaches the next walk dart. -/
theorem sigma_alpha_mem_walk :
    ∀ d ∈ ([0, 2, 4, 8, 10] : List M.Dart),
      M.sigma (M.alpha d) ∈ ([0, 2, 4, 8, 10] : List M.Dart) := by
  decide

/-- **The pocket walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_walk :
    IsNoncrossingClosedWalk M ([0, 2, 4, 8, 10] : List (Fin 14)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
      List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
        List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
          List.isChain_singleton _⟩⟩⟩⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_walk d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The pocket walk is not simple:** the darts `0` and `8` both start at `v`. -/
theorem walk_not_isSimpleClosedWalk : ¬ IsSimpleClosedWalk M ([0, 2, 4, 8, 10] : List (Fin 14)) := by
  intro h
  have hv : M.vertexOf (0 : M.Dart) = M.vertexOf (8 : M.Dart) := vertexEquiv.injective (by decide)
  have hnodup := h.vertex_nodup
  change [M.vertexOf (0 : M.Dart), M.vertexOf (2 : M.Dart), M.vertexOf (4 : M.Dart),
    M.vertexOf (8 : M.Dart), M.vertexOf (10 : M.Dart)].Nodup at hnodup
  rw [hv] at hnodup
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- **Both cells meet the walk in proper arcs.**  The cell `[3,6]` meets the walk only through the
reversal `2` of its dart `3`, and the cell `[11,12]` only through the reversal `10` of `11`; the
edges `{6,7}` and `{12,13}` are off the walk. -/
theorem properArcs :
    M.faceOf (6 : M.Dart) = M.faceOf (3 : M.Dart) ∧
      M.faceOf (12 : M.Dart) = M.faceOf (11 : M.Dart) ∧
        ∀ z ∈ ([6, 7, 12, 13] : List M.Dart), z ∉ ([0, 2, 4, 8, 10] : List M.Dart) :=
  ⟨faceEquiv.injective (by decide), faceEquiv.injective (by decide), by decide⟩

/-- **The lake with proper arcs admits no first-turn order.**  Among the walk darts, the first-turn
predecessor of `0` is `4` (one step to `5`), that of `2` is `0` (past `6` to `1`), and that of `4` is
`2` (past `7` to `3`).  So `{0, 2, 4}` is closed under predecessors, and a list in first-turn order
holding `0` would miss `8`. -/
theorem properLake_not_firstTurnOrder (p : List M.Dart) (hne : p ≠ [])
    (hsub : ∀ a ∈ p, a ∈ ([0, 2, 4, 8, 10] : List M.Dart)) (h0 : (0 : M.Dart) ∈ p)
    (h2 : (2 : M.Dart) ∈ p) (h4 : (4 : M.Dart) ∈ p) (h8 : (8 : M.Dart) ∈ p) :
    ¬ FirstTurnOrder M p hne := by
  intro hp
  have hoff : ∀ z : M.Dart, (∀ a : M.Dart, a ∈ ([0, 2, 4, 8, 10] : List M.Dart) →
      M.alpha a ≠ z ∧ M.alpha a ≠ M.alpha z) → ¬ walkKeep M (p.reverse.map M.alpha) z := by
    intro z hz hk
    rcases hk with hk | hk
    · obtain ⟨a, ha, haz⟩ := List.mem_map.mp hk
      exact (hz a (hsub a (List.mem_reverse.mp ha))).1 haz
    · obtain ⟨a, ha, haz⟩ := List.mem_map.mp hk
      exact (hz a (hsub a (List.mem_reverse.mp ha))).2 haz
  have hclosed : ∀ ⦃d e : M.Dart⦄, d ∈ p → e ∈ p →
      FirstTurn M (p.reverse.map M.alpha) (M.alpha e) (M.alpha d) →
        (e = 0 ∨ e = 2 ∨ e = 4) → (d = 0 ∨ d = 2 ∨ d = 4) := by
    intro d e hd _ h he
    rcases he with rfl | rfl | rfl
    · exact Or.inr (Or.inr (FirstTurnOrder.pred_eq_of_firstTurn h hd
        (FirstTurn.of_sigma_alpha (by decide)) h4))
    · exact Or.inl (FirstTurnOrder.pred_eq_of_firstTurn h hd
        (FirstTurn.of_sigma_sigma_alpha (hoff _ (by decide)) (by decide)) h0)
    · exact Or.inr (Or.inl (FirstTurnOrder.pred_eq_of_firstTurn h hd
        (FirstTurn.of_sigma_sigma_alpha (hoff _ (by decide)) (by decide)) h2))
  rcases hp.all_or_none (fun x => x = 0 ∨ x = 2 ∨ x = 4) hclosed with hall | hnone
  · rcases hall 8 h8 with h | h | h <;> exact absurd h (by decide)
  · exact hnone 0 h0 (Or.inl rfl)

/-- The pocket walk `[0,2,4,8,10]` of the lake with proper arcs is not in first-turn order. -/
theorem properLake_walk_not_firstTurnOrder :
    ¬ FirstTurnOrder M ([0, 2, 4, 8, 10] : List M.Dart) (List.cons_ne_nil _ _) :=
  properLake_not_firstTurnOrder _ _ (fun _ ha => ha) (by decide) (by decide) (by decide)
    (by decide)

end OsinPocketCellFirstTurnsLakeModel

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurn.eq_of_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurn.eq_sigma_alpha_of_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnOrder.pred_eq_of_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnOrder.not_of_sigma_eq_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnOrder.all_or_none
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.not_firstTurns_of_sigma_eq_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.firstTurns_all_or_none
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.multipleEdgeLake_pocketCycle_not_firstTurnOrder
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.doubleTouch_walk_not_firstTurnOrder
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.planar
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.isNoncrossingClosedWalk_walk
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.walk_not_isSimpleClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.properArcs
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellFirstTurnsLakeModel.properLake_walk_not_firstTurnOrder
