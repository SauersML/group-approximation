import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import Mathlib.GroupTheory.Perm.Fin
import GroupApproximation.Meta.AxiomGuard

/-!
# A multiple edge enclosing a lake: no pocket face set has a following outer cycle

A model test for binder 5, `OsinMultipleEdgePocketRegionSectionStatement`
(`Estimating/OsinPocketMultipleEdgeAssembly.lean`), through its input
`MultipleEdgePocketRegionInput` (`Estimating/OsinPocketRegionSide.lean`).  For two distinct
sections joining cells `i` and `j`, that input asks for a pocket region `P` with a relator cell
inside, the faces of `i` and `j` outside, and `P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary`.

The prediction put to the lead: when cell `i` lies in a lake of the pocket, no face set with the
pocket inside and `i` and `j` outside has an outer boundary cycle that follows its boundary.

The map has eight darts, the edges `{0,1}`, `{2,3}`, `{4,5}` and `{6,7}`, and two vertices: `v`
with rotation `0 ↦ 1 ↦ 2 ↦ 6 ↦ 4 ↦ 0` and `u` with rotation `3 ↦ 5 ↦ 7 ↦ 3`.  Its four faces are
the pocket `K = [0,2,5]`, the monogon `Πᵢ = [1]` inside the loop `{0,1}` at `v`, the digon
`Πⱼ = [4,7]` between the edges `{4,5}` and `{6,7}`, and the outside `O = [3,6]`.  So `Πᵢ` is a lake
of `K`: its only edge has `K` on the other side.  Informally `Πᵢ` and `Πⱼ` are joined by the
trivial path at `v` and by the edge `{2,3}` from `v` to `u`, and the pocket between the two is `K`.

* `planar`: the map is planar, with two vertices, four edges and four faces.
* `isNoncrossingClosedWalk_pocketCycle`, `pocketCycle_not_isSimpleClosedWalk`: the boundary walk
  `[0,2,5]` of `K` is a noncrossing closed walk and is not simple, since `0` and `2` both start at
  `v`.
* `pocketCycle_innerCycle_followsBoundary`: its inner cycle follows its boundary.
* `not_followsBoundary_of_monogon`: in any map, if a face set has a boundary dart `y` with
  `facePerm y = y` and a second boundary dart, then no boundary cycle of the face set follows its
  boundary.  The boundary walk from `y` stays at `y`, which is not internal, while the cyclic
  successor of `y` is another dart.
* `lake_not_followsBoundary`: on this map, no face set containing `Πᵢ` and `Πⱼ` and not `K` has a
  boundary cycle that follows its boundary.  In particular the outer cycle of the walk does not
  follow (`pocketCycle_outerCycle_not_followsBoundary`).

The outside of a pocket region is the complement of its faces, so a pocket region on this map with
`K` inside and `Πᵢ`, `Πⱼ` outside has an outer cycle that does not follow its boundary.  The
endpoint `multipleEdgeLakePrediction` records the configuration.  The model tests the map only,
with no labels, relator cells, sections or arcs.  Whether a least-area diagram with a globally
distinguished section family carries such a lake is not decided here.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketMultipleEdgeLakeModel

open Equiv
open Surgery.MapCollapse (BoundaryCycle BoundaryWalk IsBoundaryDart)

universe v

/-- `finRotate n` has no fixed point once `2 ≤ n`. -/
theorem finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  have hi : i ∈ (finRotate n).support := by
    rw [support_finRotate_of_le hn]
    exact Finset.mem_univ i
  exact Perm.mem_support.mp hi

/-- **A monogon boundary dart stops every boundary walk.**  If a face set has a boundary dart `y`
with `facePerm y = y` and another boundary dart `z`, then no boundary cycle of the face set follows
its boundary: the boundary walk from `y` stays at `y`, which is not internal, while the cyclic
successor of `y` is a different dart. -/
theorem not_followsBoundary_of_monogon {N : CombMap.{v}} {faces : Finset N.Face}
    (B : BoundaryCycle N faces) {y z : N.Dart} (hy : N.facePerm y = y)
    (hyb : IsBoundaryDart N faces y) (hzb : IsBoundaryDart N faces z) (hyz : y ≠ z) :
    ¬ B.FollowsBoundary := by
  intro h
  have hw := h ⟨y, hyb⟩
  change Relation.ReflTransGen _ (N.facePerm y) _ at hw
  rw [hy] at hw
  rcases Relation.ReflTransGen.cases_head hw with heq | ⟨_c, ⟨⟨-, hc⟩, -⟩, -⟩
  · have hrot : B.positionEquiv (finRotate B.cycle.length (B.positionEquiv.symm ⟨y, hyb⟩)) =
        ⟨y, hyb⟩ := Subtype.ext heq.symm
    have hne : ((B.positionEquiv.symm ⟨y, hyb⟩ : Fin B.cycle.length) : ℕ) ≠
        (B.positionEquiv.symm ⟨z, hzb⟩ : Fin B.cycle.length) := fun h' =>
      hyz (congrArg Subtype.val (B.positionEquiv.symm.injective (Fin.ext h')))
    have hlen : 2 ≤ B.cycle.length := by
      have h1 := (B.positionEquiv.symm ⟨y, hyb⟩).isLt
      have h2 := (B.positionEquiv.symm ⟨z, hzb⟩).isLt
      omega
    exact finRotate_ne_self hlen _
      (B.positionEquiv.injective (hrot.trans (B.positionEquiv.apply_symm_apply _).symm))
  · exact hyb.2 hc

def lakeAlpha : Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

def lakeSigma : Perm (Fin 8) where
  toFun := ![1, 2, 6, 5, 0, 7, 4, 3]
  invFun := ![4, 0, 1, 7, 6, 3, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The multiple edge enclosing a lake. -/
def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := lakeAlpha
  sigma := lakeSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

def faceClass : Fin 8 → Fin 4 := ![0, 1, 0, 2, 3, 0, 2, 3]
def faceRep : Fin 4 → Fin 8 := ![0, 1, 3, 4]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 1, 0, 1, 0, 1] : Fin 8 → Fin 2)
    (![0, 3] : Fin 2 → Fin 8) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h26 : Relation.EqvGen M.Adjacent 2 6 := .rel _ _ (Or.inr rfl)
      have h35 : Relation.EqvGen M.Adjacent 3 5 := .rel _ _ (Or.inr rfl)
      have h57 : Relation.EqvGen M.Adjacent 5 7 := .rel _ _ (Or.inr rfl)
      have h64 : Relation.EqvGen M.Adjacent 6 4 := .rel _ _ (Or.inr rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 := .trans _ _ _ h01 h12
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .trans _ _ _ h02 h23
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .trans _ _ _ h03 h35
      have h06 : Relation.EqvGen M.Adjacent 0 6 := .trans _ _ _ h02 h26
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact .trans _ _ _ h06 h64
      · exact h05
      · exact h06
      · exact .trans _ _ _ h05 h57
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 8 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 4 := by omega
    rw [heq]
    norm_num

/-- One rotation step from the reversal of each dart of the pocket walk reaches a dart of the
walk. -/
theorem sigma_alpha_mem_pocketCycle :
    ∀ d ∈ ([0, 2, 5] : List M.Dart), M.sigma (M.alpha d) ∈ ([0, 2, 5] : List M.Dart) := by
  decide

/-- **The boundary walk of the pocket is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_pocketCycle :
    IsNoncrossingClosedWalk M ([0, 2, 5] : List (Fin 8)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_pocketCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The pocket walk is not a simple closed walk:** the darts `0` and `2` both start at `v`. -/
theorem pocketCycle_not_isSimpleClosedWalk :
    ¬ IsSimpleClosedWalk M ([0, 2, 5] : List (Fin 8)) := by
  intro h
  have hv : M.vertexOf (0 : M.Dart) = M.vertexOf (2 : M.Dart) := vertexEquiv.injective (by decide)
  have hnodup := h.vertex_nodup
  change [M.vertexOf (0 : M.Dart), M.vertexOf (2 : M.Dart), M.vertexOf (5 : M.Dart)].Nodup
    at hnodup
  rw [hv] at hnodup
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- A face step is a boundary walk. -/
theorem boundaryWalk_of_facePerm_eq (faces : Finset M.Face) {d e : M.Dart}
    (h : M.facePerm d = e) : BoundaryWalk M faces d e := by
  change Relation.ReflTransGen _ (M.facePerm d) e
  subst h
  exact Relation.ReflTransGen.refl

theorem innerCycle_pocketCycle :
    (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).cycle = ([0, 2, 5] : List (Fin 8)) := by
  decide

theorem innerCycle_pocketCycle_getLast :
    (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).cycle.getLast
      (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).cycle_nonempty = 5 := by
  decide

theorem innerCycle_pocketCycle_head :
    (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).cycle.head
      (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).cycle_nonempty = 0 := by
  decide

/-- **The inner cycle of the pocket walk follows its boundary:** `0 ↦ 2`, `2 ↦ 5` and `5 ↦ 0` are
face steps of `K`. -/
theorem pocketCycle_innerCycle_followsBoundary :
    (isNoncrossingClosedWalk_pocketCycle.innerCycle planar).FollowsBoundary := by
  refine Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · rw [innerCycle_pocketCycle]
    exact List.isChain_cons_cons.mpr ⟨boundaryWalk_of_facePerm_eq _ (by decide),
      List.isChain_cons_cons.mpr ⟨boundaryWalk_of_facePerm_eq _ (by decide),
        List.isChain_singleton _⟩⟩
  · rw [innerCycle_pocketCycle_getLast, innerCycle_pocketCycle_head]
    exact boundaryWalk_of_facePerm_eq _ (by decide)

/-- **No face set around the lake has a following boundary cycle.**  A face set containing the lake
`Πᵢ` and the digon `Πⱼ` but not the pocket `K` has the boundary darts `1` and `4`, and `1` is the
only dart of its face. -/
theorem lake_not_followsBoundary (outside : Finset M.Face)
    (hi : M.faceOf (1 : M.Dart) ∈ outside) (hj : M.faceOf (4 : M.Dart) ∈ outside)
    (hK : M.faceOf (0 : M.Dart) ∉ outside) (B : BoundaryCycle M outside) :
    ¬ B.FollowsBoundary := by
  have h50 : M.faceOf (5 : M.Dart) = M.faceOf (0 : M.Dart) := faceEquiv.injective (by decide)
  refine not_followsBoundary_of_monogon B (y := 1) (z := 4) (by decide) ⟨hi, ?_⟩ ⟨hj, ?_⟩
    (by decide)
  · rw [show M.alpha (1 : M.Dart) = 0 by decide]
    exact hK
  · rw [show M.alpha (4 : M.Dart) = 5 by decide, h50]
    exact hK

/-- **The outer cycle of the pocket walk does not follow its boundary:** the monogon dart `1` and
the dart `4` of `Πⱼ` are boundary darts of the outer side. -/
theorem pocketCycle_outerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_pocketCycle.outerCycle planar).FollowsBoundary :=
  not_followsBoundary_of_monogon _ (by decide)
    ((isNoncrossingClosedWalk_pocketCycle.isBoundaryDart_sideOutside_iff planar 1).mpr (by decide))
    ((isNoncrossingClosedWalk_pocketCycle.isBoundaryDart_sideOutside_iff planar 4).mpr (by decide))
    (by decide)

/-- **A multiple edge enclosing a lake** (model test).  There is a planar map with a noncrossing
closed walk `w` that is not simple and two walk darts `x₁`, `x₃` on one face, such that
* the face across `x₁` is a monogon, different from the face across `x₃`;
* the inner cycle of `w` follows its boundary and the outer cycle does not;
* no face set containing the faces across `x₁` and `x₃` and not the face of `x₁` has a boundary
  cycle that follows its boundary. -/
def MultipleEdgeLakePrediction : Prop :=
  ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (w : List N.Dart) (hw : IsNoncrossingClosedWalk N w)
      (x₁ x₃ : N.Dart),
    x₁ ∈ w ∧ x₃ ∈ w ∧ N.faceOf x₁ = N.faceOf x₃ ∧ N.facePerm (N.alpha x₁) = N.alpha x₁ ∧
      N.faceOf (N.alpha x₁) ≠ N.faceOf (N.alpha x₃) ∧ ¬ IsSimpleClosedWalk N w ∧
      (hw.innerCycle hN).FollowsBoundary ∧ ¬ (hw.outerCycle hN).FollowsBoundary ∧
      ∀ outside : Finset N.Face, N.faceOf (N.alpha x₁) ∈ outside →
        N.faceOf (N.alpha x₃) ∈ outside → N.faceOf x₁ ∉ outside →
          ∀ B : BoundaryCycle N outside, ¬ B.FollowsBoundary

theorem multipleEdgeLakePrediction : MultipleEdgeLakePrediction := by
  refine ⟨M, planar, _, isNoncrossingClosedWalk_pocketCycle, 0, 5, by decide, by decide,
    faceEquiv.injective (by decide), by decide,
    fun h => absurd (congrArg faceEquiv h) (by decide), pocketCycle_not_isSimpleClosedWalk,
    pocketCycle_innerCycle_followsBoundary, pocketCycle_outerCycle_not_followsBoundary,
    fun outside hi hj hK => ?_⟩
  rw [show M.alpha (0 : M.Dart) = 1 by decide] at hi
  rw [show M.alpha (5 : M.Dart) = 4 by decide] at hj
  exact lake_not_followsBoundary outside hi hj hK

#audit_axioms finRotate_ne_self
#audit_axioms not_followsBoundary_of_monogon
#audit_closed_axioms planar
#audit_closed_axioms isNoncrossingClosedWalk_pocketCycle
#audit_axioms pocketCycle_not_isSimpleClosedWalk
#audit_closed_axioms pocketCycle_innerCycle_followsBoundary
#audit_axioms lake_not_followsBoundary
#audit_axioms pocketCycle_outerCycle_not_followsBoundary
#audit_closed_axioms multipleEdgeLakePrediction

end GroupApproximation.GGT.VanKampen.OsinPocketMultipleEdgeLakeModel
