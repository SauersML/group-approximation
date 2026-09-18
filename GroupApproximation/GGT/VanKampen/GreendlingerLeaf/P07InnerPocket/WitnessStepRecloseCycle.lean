import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.SurgeryFaceNew
import GroupApproximation.GGT.VanKampen.FiniteCycleSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-62: the collapsed set and its following boundary cycle

Lane gl-p07-62.  For an `EnclosedFaceSetSucc X F ow` whose walk darts all have their reverse in
`F`, the collapsed face set `O = univ \ F` (the complement of the pocket middle) has **exactly**
the darts of `ow` as its boundary darts, and `ow` itself, as a `BoundaryCycle` of `O`, follows its
boundary.  Certifies no printed sentence on its own.  NOT COMPILED: authored without running Lean.

## The mathematical proof

* *Boundary darts* (`witnessStepReclose_isBoundary_iff`).  `mem_iff` reads
  `d ∈ ow ↔ face d ∉ F ∧ (face (α d) ∈ F ∨ α d ∈ ow)`.  With `face (α d) ∈ F` on the walk, this is
  `face d ∈ O ∧ face (α d) ∉ O`.
* *One step* (`witnessStepReclose_step`).  If `y` is on no walk edge and `face y ∉ F`, then
  `face (α y) ∉ F` (else `y ∈ ow` by `mem_iff`).  So `y` is internal to `O`, and
  `face (σ y) = face (facePerm (α y)) = face (α y) ∉ F`.
* *Walk* (`witnessStepReclose_walk`).  From `d ∈ ow`, the darts `σ^k (α d)`, `0 < k ≤ m`, before the
  first kept one are reached from `facePerm d = σ (α d)` along internal `σ`-steps.
* *Follows* (`witnessStepReclose_followsBoundary`).  At `ow[i]` the first kept dart is
  `ow[(i+1) % |ow|]` (`turn_next`), which is the cyclic successor on the cycle.

No planarity and no hypothesis of the pocket is used beyond `EnclosedFaceSetSucc` and `hnb`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open SimpleClosedWalkSides Surgery.MapCollapse

universe u w v

/-- **The collapsed face set**: the complement of `F`. -/
noncomputable def witnessStepReclose_faces (M : CombMap.{v}) (F : Finset M.Face) :
    Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => f ∉ F

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_faces

/-- Membership in the collapsed face set. -/
theorem witnessStepReclose_mem_faces {M : CombMap.{v}} {F : Finset M.Face} {f : M.Face} :
    f ∈ witnessStepReclose_faces M F ↔ f ∉ F := by
  classical
  unfold witnessStepReclose_faces
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_mem_faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The walk darts are exactly the boundary darts of the collapsed set.** -/
theorem witnessStepReclose_isBoundary_iff {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) (d : X.toCombMap.Dart) :
    d ∈ ow ↔ Surgery.MapCollapse.IsBoundaryDart X.toCombMap
      (witnessStepReclose_faces X.toCombMap F) d := by
  unfold Surgery.MapCollapse.IsBoundaryDart
  rw [witnessStepReclose_mem_faces, witnessStepReclose_mem_faces, not_not]
  constructor
  · intro hd
    exact ⟨((E.mem_iff d).mp hd).1, hnb d hd⟩
  · intro h
    exact (E.mem_iff d).mpr ⟨h.1, Or.inl h.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_isBoundary_iff

/-- **One step off the walk.**  A dart on no walk edge, based off `F`, is internal to the collapsed
set, and its vertex rotation is again based off `F`. -/
theorem witnessStepReclose_step {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow) {y : X.toCombMap.Dart}
    (hnk : ¬ walkKeep X.toCombMap ow y) (hy : X.toCombMap.faceOf y ∉ F) :
    InternalDart X.toCombMap (witnessStepReclose_faces X.toCombMap F) y ∧
      X.toCombMap.faceOf (X.toCombMap.sigma y) ∉ F := by
  have hay : X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ F := fun hin =>
    hnk (Or.inl ((E.mem_iff y).mpr ⟨hy, Or.inl hin⟩))
  have hfp : X.toCombMap.facePerm (X.toCombMap.alpha y) = X.toCombMap.sigma y := by
    rw [PocketRun.facePerm_eq_sigma_alpha, X.toCombMap.alpha_involutive y]
  refine ⟨⟨witnessStepReclose_mem_faces.mpr hy, witnessStepReclose_mem_faces.mpr hay⟩, ?_⟩
  rw [← hfp, X.toCombMap.faceOf_facePerm]
  exact hay

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_step

/-- **The boundary walk up to the first kept dart.**  From a walk dart `d`, every `σ^k (α d)` with
`0 < k ≤ m`, where no `σ^k (α d)` with `0 < k < m` is kept, is based off `F` and is reached from
`facePerm d` by internal vertex rotations of the collapsed set. -/
theorem witnessStepReclose_walk {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow) {d : X.toCombMap.Dart} (hd : d ∈ ow) {m : ℕ}
    (hfirst : ∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap ow
      ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) :
    ∀ k, 0 < k → k ≤ m →
      X.toCombMap.faceOf ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d)) ∉ F ∧
        BoundaryWalk X.toCombMap (witnessStepReclose_faces X.toCombMap F) d
          ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact absurd hk (Nat.lt_irrefl 0)
  | succ k ih =>
    intro _ hkm
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [Nat.zero_add, pow_one, ← PocketRun.facePerm_eq_sigma_alpha,
        X.toCombMap.faceOf_facePerm]
      refine ⟨((E.mem_iff d).mp hd).1, ?_⟩
      unfold BoundaryWalk
      exact Relation.ReflTransGen.refl
    · obtain ⟨hy, hB⟩ := ih hpos (Nat.le_of_succ_le hkm)
      obtain ⟨hint, hσ⟩ :=
        witnessStepReclose_step E (hfirst k hpos (Nat.lt_of_succ_le hkm)) hy
      rw [pow_succ', Equiv.Perm.mul_apply]
      refine ⟨hσ, ?_⟩
      unfold BoundaryWalk at hB ⊢
      exact Relation.ReflTransGen.tail hB ⟨hint, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_walk

/-- **The walk as a boundary cycle of the collapsed set.** -/
noncomputable def witnessStepReclose_cycle {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) :
    BoundaryCycle X.toCombMap (witnessStepReclose_faces X.toCombMap F) where
  cycle := ow
  cycle_nonempty := E.ne_nil
  cycle_nodup := E.nodup
  cycle_mem_iff := witnessStepReclose_isBoundary_iff E hnb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_cycle

/-- The cycle of `witnessStepReclose_cycle` is the walk. -/
theorem witnessStepReclose_cycle_cycle {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) :
    (witnessStepReclose_cycle E hnb).cycle = ow :=
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_cycle_cycle

/-- The cyclic successor index on a list of positive length. -/
theorem witnessStepReclose_finRotate_val {n i : ℕ} (hi : i < n) :
    (finRotate n ⟨i, hi⟩).val = (i + 1) % n := by
  rw [FiniteCycleSplit.rotate_val]
  split
  · rename_i h
    have h' : i + 1 = n := h
    rw [h', Nat.mod_self]
  · rename_i h
    have h' : i + 1 ≠ n := h
    exact (Nat.mod_eq_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hi) h')).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_finRotate_val

/-- **The walk follows the boundary of the collapsed set.**  At `ow[i]`, the first kept dart after
`α ow[i]` is `ow[(i+1) % |ow|]` (`turn_next`), reached from `facePerm ow[i]` by internal vertex
rotations (`witnessStepReclose_walk`); it is the cyclic successor on the cycle. -/
theorem witnessStepReclose_followsBoundary {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) :
    (witnessStepReclose_cycle E hnb).FollowsBoundary := by
  intro d
  have hd : d.1 ∈ ow := (witnessStepReclose_isBoundary_iff E hnb d.1).mpr d.2
  obtain ⟨i, hi, hdi⟩ := List.mem_iff_getElem.mp hd
  have hpos : 0 < ow.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  obtain ⟨m, hm, hkeep, hmin⟩ := PocketRun.exists_firstKeep ow (List.getElem_mem hi)
  have hnext := E.turn_next i hi m hm hkeep hmin
  have hwalk := (witnessStepReclose_walk E (List.getElem_mem hi) hmin m hm le_rfl).2
  rw [hnext] at hwalk
  have hperm : ((witnessStepReclose_cycle E hnb).boundaryPerm d).1 =
      ow[(i + 1) % ow.length]'(Nat.mod_lt _ hpos) := by
    rw [boundaryPerm_val_of_getElem X.toCombMap _ (witnessStepReclose_cycle E hnb) i hi d
      hdi.symm, List.get_eq_getElem]
    exact getElem_index_congr ow (witnessStepReclose_finRotate_val hi) _ _
  rw [hperm, ← hdi]
  exact hwalk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepReclose_followsBoundary

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
