import GroupApproximation.GGT.VanKampen.SurgeryNoncrossingCollarWalkSides
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Model test for the corner join of a noncrossing strip

Stage 3 of the geodesic collar (`GeodesicCollar.joinStatement`) joins the corners of a strip face
`p ++ q` whose side `p` has value one.  Its `CornerJoin.Input` uses the corners
`x = alpha (q.getLast)`, which rotates to the start of `p`, and `y = alpha (p.getLast)`, which starts
where the rest `r` of the walk `p ++ r` starts.  The field `not_same_vertex : ¬ sigma.SameCycle x y`
comes from `vertex_nodup` of the simple walk `p ++ r`.

A noncrossing closed walk whose outer cycle follows its boundary can start `p` and `r` at one
vertex.  The model `pinchedJoin` is a planar map with one vertex, three loops and four faces: the
strip face `{0, 2}`, the face `{3}` across the strip, the face `{4}` of the rest and the outside
`{1, 5}`.  The walk `[0, 4]` bounds the first three faces, is noncrossing, turns back and is not
simple, and the corners `alpha 2 = 3` and `alpha 0 = 1` lie in one rotation cycle
(`pinchedJoinModel`).

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through
Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels

open Equiv NoncrossingCollarWalk

/-- The reversal of the pinched join, `(0 1)(2 3)(4 5)`. -/
def pinchedJoinAlpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The rotation of the pinched join, `0 → 5 → 4 → 1 → 2 → 3 → 0`. -/
def pinchedJoinSigma : Perm (Fin 6) where
  toFun := ![5, 2, 3, 0, 1, 4]
  invFun := ![3, 4, 1, 2, 5, 0]
  left_inv := by decide
  right_inv := by decide

/-- Three loops at one vertex, with the strip face `{0, 2}` meeting the face `{4}` there. -/
def pinchedJoin : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := pinchedJoinAlpha
  sigma := pinchedJoinSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq pinchedJoin.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat pinchedJoin.Dart n := inferInstanceAs (OfNat (Fin 6) n)

/-- The faces `{0, 2}`, `{1, 5}`, `{3}` and `{4}`. -/
def faceClass : Fin 6 → Fin 4 := ![0, 1, 0, 2, 3, 1]
def faceRep : Fin 4 → Fin 6 := ![0, 1, 3, 4]

noncomputable def faceEquiv : pinchedJoin.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv pinchedJoin.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 4) : pinchedJoin.Face := pinchedJoin.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 4) :
    pinchedJoin.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : pinchedJoin.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv pinchedJoin.sigma (![0, 0, 0, 0, 0, 0] : Fin 6 → Fin 1)
    (![0] : Fin 1 → Fin 6) (by decide) (by decide) (by decide)

/-- The pinched join has one vertex. -/
theorem vertexOf_eq (d e : pinchedJoin.Dart) : pinchedJoin.vertexOf d = pinchedJoin.vertexOf e :=
  vertexEquiv.injective (Subsingleton.elim _ _)

theorem pinchedJoin_planar : pinchedJoin.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen pinchedJoin.Adjacent 0 d := by
      have h05 : Relation.EqvGen pinchedJoin.Adjacent 0 5 := .rel _ _ (Or.inr rfl)
      have h54 : Relation.EqvGen pinchedJoin.Adjacent 5 4 := .rel _ _ (Or.inr rfl)
      have h41 : Relation.EqvGen pinchedJoin.Adjacent 4 1 := .rel _ _ (Or.inr rfl)
      have h12 : Relation.EqvGen pinchedJoin.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen pinchedJoin.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      have h04 := Relation.EqvGen.trans _ _ _ h05 h54
      have h01 := Relation.EqvGen.trans _ _ _ h04 h41
      have h02 := Relation.EqvGen.trans _ _ _ h01 h12
      have h03 := Relation.EqvGen.trans _ _ _ h02 h23
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : pinchedJoin.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : pinchedJoin.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : pinchedJoin.dartCount = 6 := by simp [CombMap.dartCount, pinchedJoin]
    have he := pinchedJoin.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : pinchedJoin.edgeCount = 3 := by omega
    rw [heq]
    norm_num

/-- **The walk `[0, 4]` is a noncrossing closed walk**: the side `[0]` of the strip and the
rest `[4]`. -/
theorem isNoncrossingClosedWalk_joinCycle :
    IsNoncrossingClosedWalk pinchedJoin ([0, 4] : List pinchedJoin.Dart) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexOf_eq _ _, List.isChain_singleton _⟩
  closes := vertexOf_eq _ _
  alpha_not_mem := by decide
  turn_mem d hd := by
    rcases List.mem_cons.mp hd with rfl | hd
    · refine NoncrossingClosedWalkSides.turn_mem_of_first (m₀ := 3) (by norm_num) ?_ ?_
      · rw [pow_succ, pow_succ, pow_one, Perm.mul_apply, Perm.mul_apply]
        decide
      · intro k hk0 hk3
        obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
        · rw [pow_one]
          unfold SimpleClosedWalkSides.walkKeep
          decide
        · rw [pow_succ, pow_one, Perm.mul_apply]
          unfold SimpleClosedWalkSides.walkKeep
          decide
    · rcases List.mem_singleton.mp hd with rfl
      exact NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
        (by rw [pow_one]; decide)
        fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The walk turns back**: one rotation step from each walk dart is the reversal of the other. -/
theorem outerTurn_joinCycle : OuterTurn pinchedJoin ([0, 4] : List pinchedJoin.Dart) where
  chain := List.isChain_cons_cons.mpr
    ⟨⟨1, Nat.one_pos, by rw [pow_one]; decide,
        fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩,
      List.isChain_singleton _⟩
  closes _ := ⟨1, Nat.one_pos,
    show (pinchedJoin.sigma ^ 1) 0 = pinchedJoin.alpha 4 by rw [pow_one]; decide,
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩

/-- The strip face `[0, 2]`: the side `[0]` and the other side `[2]`. -/
theorem isFaceCycle_joinFace : pinchedJoin.IsFaceCycle ([0, 2] : List pinchedJoin.Dart) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨by decide, List.isChain_singleton _⟩
  closes := by decide

/-- The strip face, the face across the strip and the face of the rest. -/
def joinFaces : Finset pinchedJoin.Face :=
  Finset.cons (face 0) (Finset.cons (face 2) {face 3} fun h =>
      absurd ((face_eq_iff 2 3).mp (Finset.mem_singleton.mp h)) (by decide))
    fun h => by
      rcases Finset.mem_cons.mp h with h | h
      · exact absurd ((face_eq_iff 0 2).mp h) (by decide)
      · exact absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

/-- The other side `[2]` of the strip is inside the face set. -/
theorem alpha_mem_joinFaces :
    ∀ e ∈ ([2] : List pinchedJoin.Dart), pinchedJoin.faceOf (pinchedJoin.alpha e) ∈ joinFaces := by
  intro e he
  rcases List.mem_singleton.mp he with rfl
  exact Finset.mem_cons.mpr (Or.inr (Finset.mem_cons.mpr (Or.inl rfl)))

/-- The boundary of the face set is the walk `[0, 4]`. -/
theorem isBoundaryDart_joinFaces_iff (d : Fin 6) :
    Surgery.MapCollapse.IsBoundaryDart pinchedJoin joinFaces d ↔
      d ∈ ([0, 4] : List pinchedJoin.Dart) := by
  change (pinchedJoin.faceOf d ∈ joinFaces ∧
    pinchedJoin.faceOf (pinchedJoin.alpha d) ∉ joinFaces) ↔ _
  simp only [joinFaces, Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- Any two darts of the pinched join lie in one rotation cycle. -/
theorem sameCycle (d e : pinchedJoin.Dart) : pinchedJoin.sigma.SameCycle d e :=
  (pinchedJoin.vertexOf_eq_iff d e).mp (vertexOf_eq d e)

/-- **The walk `[0, 4]` is not simple:** both darts start at the one vertex. -/
theorem joinCycle_not_isSimpleClosedWalk :
    ¬ IsSimpleClosedWalk pinchedJoin ([0, 4] : List pinchedJoin.Dart) := by
  intro h
  have hnodup := h.vertex_nodup
  change [pinchedJoin.vertexOf (0 : pinchedJoin.Dart),
    pinchedJoin.vertexOf (4 : pinchedJoin.Dart)].Nodup at hnodup
  rw [vertexOf_eq 4 0] at hnodup
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- **A pinched corner join** (model test).  There is a planar map with a strip face `p ++ q` and
a face set whose boundary is a noncrossing closed walk `p ++ r`, `r ≠ []`, whose outer cycle follows
its boundary, with the other side `q` inside the face set, such that the join corners
`alpha (q.getLast)` and `alpha (p.getLast)` lie in one rotation cycle.  The walk is not simple. -/
def PinchedJoinModel : Prop :=
  ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (S : Finset N.Face) (p q r : List N.Dart) (hp : p ≠ [])
    (hq : q ≠ []) (hw : IsNoncrossingClosedWalk N (p ++ r)),
    r ≠ [] ∧ N.IsFaceCycle (p ++ q) ∧ (∀ e ∈ q, N.faceOf (N.alpha e) ∈ S) ∧
      (∀ d, Surgery.MapCollapse.IsBoundaryDart N S d ↔ d ∈ p ++ r) ∧
      (hw.outerCycle hN).FollowsBoundary ∧
      N.sigma.SameCycle (N.alpha (q.getLast hq)) (N.alpha (p.getLast hp)) ∧
      ¬ IsSimpleClosedWalk N (p ++ r)

theorem pinchedJoinModel : PinchedJoinModel :=
  ⟨pinchedJoin, pinchedJoin_planar, joinFaces, [0], [2], [4], List.cons_ne_nil _ _,
    List.cons_ne_nil _ _, isNoncrossingClosedWalk_joinCycle, List.cons_ne_nil _ _,
    isFaceCycle_joinFace, alpha_mem_joinFaces, isBoundaryDart_joinFaces_iff,
    followsBoundary_outerCycle _ pinchedJoin_planar outerTurn_joinCycle, sameCycle _ _,
    joinCycle_not_isSimpleClosedWalk⟩

end GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels

#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels.pinchedJoin_planar
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels.isNoncrossingClosedWalk_joinCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels.outerTurn_joinCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoinModels.pinchedJoinModel
