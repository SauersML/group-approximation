import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketArcTrim
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.Walk
import GroupApproximation.Meta.AxiomGuard

/-!
# Absorbing a full source cell into the pocket (piece 08, Case B)

Let `K` be a `PocketFaceSet` in walk order whose source arc `t_1` is the whole boundary of the
source cell `Π = cell K.source`, with face `p`, and let `k` be a relator cell whose face lies
outside `insert p K.faces`.  Then `absorbSource K hfull k hk` is a pocket face set with faces
`insert p K.faces`, source `k`, the empty source arc, and the same sides and target arc; it is in
walk order and its source arc is proper.

* Boundary darts.  A dart `d` is a boundary dart of `insert p faces` iff it lies in
  `s_1 ++ s_2 ++ t_2`.  The reversed full arc `invDarts t_1` is exactly the set of darts `e` with
  `faceOf (alpha e) = p`.  A dart of `s_1 s_2 t_2` is a boundary dart of `faces` outside
  `invDarts t_1`, so its reverse is outside `faces` and not in `p`.  Conversely a boundary dart
  of `insert p faces` cannot lie in `p` (its reverse would lie in `invDarts t_1`, hence in
  `faces`), so it is a boundary dart of `faces` whose reverse is not in `p`.
* Nonempty.  `insert p faces` misses the exterior face and contains `p`; if it had no boundary
  dart it would be closed under `alpha` and `sigma`, hence contain every face by connectivity,
  the exterior included.
* Walk order.  The reversed full arc `invDarts t_1` is a closed walk: it starts at the vertex
  after the last dart `x` of `t_1` and ends at the start vertex of the first dart `y`, and
  `facePerm x = y`.  Removing a closed stretch from a closed walk leaves a closed walk.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

universe u w v

open Embedded HullSC WordMetric
open scoped Classical

/-- The empty cyclic arc at the base position. -/
def emptyArc {Dart : Type v} (cycle : List Dart) : CyclicArc cycle where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem emptyArc_darts {Dart : Type v} (cycle : List Dart) : (emptyArc cycle).darts = [] :=
  rfl

section Absorb

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

theorem invDarts_nil : invDarts X [] = [] :=
  rfl

theorem mem_invDarts_iff (t : List X.toCombMap.Dart) (d : X.toCombMap.Dart) :
    d ∈ invDarts X t ↔ X.toCombMap.alpha d ∈ t := by
  show d ∈ t.reverse.map X.toCombMap.alpha ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [X.toCombMap.alpha_involutive]
    exact List.mem_reverse.mp he
  · intro h
    exact ⟨X.toCombMap.alpha d, List.mem_reverse.mpr h, X.toCombMap.alpha_involutive d⟩

/-- The darts of a full source arc are the darts of the source face. -/
theorem mem_sourceArc_iff_of_full (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) (d : X.toCombMap.Dart) :
    d ∈ K.sourceArc.darts ↔ X.toCombMap.faceOf d = (cell X K.source).face := by
  rw [PocketFullArc.darts_eq_rotate_of_full K.sourceArc hfull, List.mem_rotate]
  exact (X.faceBoundary (cell X K.source).face).mem_iff d

/-- A nonempty face set missing the exterior face has a boundary dart. -/
theorem exists_boundaryDart (faces : Finset X.toCombMap.Face) (hout : X.outerFace ∉ faces)
    {f : X.toCombMap.Face} (hf : f ∈ faces) :
    ∃ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d := by
  by_contra hno
  have hclosed : ∀ u, X.toCombMap.faceOf u ∈ faces →
      X.toCombMap.faceOf (X.toCombMap.alpha u) ∈ faces := by
    intro u hu
    by_contra ha
    exact hno ⟨u, hu, ha⟩
  have hadj : ∀ u, X.toCombMap.faceOf (X.toCombMap.alpha u) ∈ faces ↔
      X.toCombMap.faceOf u ∈ faces := by
    intro u
    refine ⟨fun h => ?_, hclosed u⟩
    have h' := hclosed (X.toCombMap.alpha u) h
    rwa [X.toCombMap.alpha_involutive u] at h'
  have hsig : ∀ u, X.toCombMap.faceOf (X.toCombMap.sigma u) =
      X.toCombMap.faceOf (X.toCombMap.alpha u) := by
    intro u
    have h : X.toCombMap.sigma u = X.toCombMap.facePerm (X.toCombMap.alpha u) := by
      show X.toCombMap.sigma u = (X.toCombMap.sigma * X.toCombMap.alpha) (X.toCombMap.alpha u)
      rw [Equiv.Perm.mul_apply, X.toCombMap.alpha_involutive u]
    rw [h, X.toCombMap.faceOf_facePerm]
  have heqv : ∀ x y, Relation.EqvGen X.toCombMap.Adjacent x y →
      (X.toCombMap.faceOf x ∈ faces ↔ X.toCombMap.faceOf y ∈ faces) := by
    intro x y h
    induction h with
    | rel x y hxy =>
      rcases hxy with rfl | rfl
      · exact (hadj x).symm
      · rw [hsig x]
        exact (hadj x).symm
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  revert hf
  refine Quotient.inductionOn' f ?_
  intro d hd
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 ∈ (X.faceBoundary X.outerFace).darts :=
    ⟨_, List.head_mem (X.faceBoundary X.outerFace).nonempty⟩
  have h := (heqv d d0 (X.toCombMap.connected_of_planar X.planar d d0)).mp hd
  rw [((X.faceBoundary X.outerFace).mem_iff d0).mp hd0] at h
  exact hout h

/-- The cycle with the reversed source arc removed has no repeated darts. -/
theorem nodup_absorbCycle (K : PocketFaceSet D eps X lo hi) :
    (K.firstSide ++ K.secondSide ++ K.targetArc.darts).Nodup := by
  have hnd : (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts).Nodup := by
    rw [← K.decomposition]
    exact K.boundary.cycle_nodup
  exact nodup_skip hnd

/-- The cycle with the reversed full source arc removed lists the boundary darts of the face set
with the source face added. -/
theorem mem_absorbCycle_iff (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) (d : X.toCombMap.Dart) :
    d ∈ K.firstSide ++ K.secondSide ++ K.targetArc.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap
        (insert (cell X K.source).face K.faces) d := by
  have hnd : (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts).Nodup := by
    rw [← K.decomposition]
    exact K.boundary.cycle_nodup
  have hmemC : ∀ e, e ∈ K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts ↔ Surgery.MapCollapse.IsBoundaryDart X.toCombMap K.faces e := by
    intro e
    rw [← K.decomposition]
    exact K.boundary.cycle_mem_iff e
  have hA : ∀ e, e ∈ invDarts X K.sourceArc.darts ↔
      X.toCombMap.faceOf (X.toCombMap.alpha e) = (cell X K.source).face := by
    intro e
    rw [mem_invDarts_iff, mem_sourceArc_iff_of_full K hfull]
  constructor
  · intro hd
    obtain ⟨h1, h2⟩ := (hmemC d).mp (mem_of_mem_skip hd)
    refine ⟨Finset.mem_insert_of_mem h1, ?_⟩
    rw [Finset.mem_insert, not_or]
    exact ⟨fun hp => not_mem_mid_of_nodup hnd hd ((hA d).mpr hp), h2⟩
  · rintro ⟨h1, h2⟩
    rw [Finset.mem_insert, not_or] at h2
    rcases Finset.mem_insert.mp h1 with hp | hf
    · exfalso
      have hsrc : X.toCombMap.alpha d ∈ invDarts X K.sourceArc.darts := by
        rw [hA, X.toCombMap.alpha_involutive]
        exact hp
      obtain ⟨h3, -⟩ := (hmemC _).mp (mem_mid hsrc)
      exact h2.2 h3
    · exact mem_of_mem_mid_append ((hmemC d).mpr ⟨hf, h2.2⟩) (fun hi => h2.1 ((hA d).mp hi))

/-- The absorbed cycle is nonempty. -/
theorem absorbCycle_ne_nil (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) :
    K.firstSide ++ K.secondSide ++ K.targetArc.darts ≠ [] := by
  intro hnil
  have hout : X.outerFace ∉ insert (cell X K.source).face K.faces := by
    rw [Finset.mem_insert, not_or]
    exact ⟨fun h => (cell X K.source).face_ne_outer h.symm, K.outerFace_not_mem⟩
  obtain ⟨d, hd⟩ := exists_boundaryDart (insert (cell X K.source).face K.faces) hout
    (Finset.mem_insert_self (cell X K.source).face K.faces)
  have hmem := (mem_absorbCycle_iff K hfull d).mpr hd
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

/-- The reversed full source arc is a closed walk. -/
theorem walk_invDarts_full (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length)
    {r₁ r₂ : X.toCombMap.Vertex}
    (h : Walk (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)) X.toCombMap.vertexOf r₁
      (invDarts X K.sourceArc.darts) r₂) : r₁ = r₂ := by
  have hne : K.sourceArc.darts ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [CyclicArc.darts_length, hfull]
    exact List.length_pos_iff.mpr (X.faceBoundary (cell X K.source).face).nonempty
  have hlastfirst : X.toCombMap.facePerm (K.sourceArc.darts.getLast hne) =
      K.sourceArc.darts.head hne :=
    PocketFaceSet.facePerm_sourceArc_of_full K hfull _
      (by rw [List.getLast?_eq_some_getLast hne]; exact Option.mem_some_iff.mpr rfl)
      _ (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_iff.mpr rfl)
  have h1 := h
  rw [PocketFaceSet.invDarts_eq_getLast_cons hne, walk_cons] at h1
  rw [PocketFaceSet.invDarts_eq_tail_append hne, walk_append_iff] at h
  obtain ⟨r, -, hr⟩ := h
  rw [walk_cons, walk_nil] at hr
  rw [← h1.1, ← hr.2, X.toCombMap.alpha_involutive, PocketFullArc.vertexOf_alpha_eq_facePerm,
    hlastfirst]

/-- **Absorb the full source cell.**  The face set with the source face added, a new source
cell `k` outside it, the empty source arc, and the same sides and target arc. -/
noncomputable def absorbSource (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) (k : Fin X.rCellCount)
    (hk : (cell X k).face ∉ insert (cell X K.source).face K.faces) :
    PocketFaceSet D eps X lo hi where
  faces := insert (cell X K.source).face K.faces
  outerFace_not_mem := by
    rw [Finset.mem_insert, not_or]
    exact ⟨fun h => (cell X K.source).face_ne_outer h.symm, K.outerFace_not_mem⟩
  source := k
  source_not_mem := hk
  kept := K.kept
  kept_mem := Finset.mem_insert_of_mem K.kept_mem
  sourceArc := emptyArc (cellDarts X k)
  targetArc := K.targetArc
  firstSide := K.firstSide
  secondSide := K.secondSide
  boundary :=
    { cycle := K.firstSide ++ K.secondSide ++ K.targetArc.darts
      cycle_nonempty := absorbCycle_ne_nil K hfull
      cycle_nodup := nodup_absorbCycle K
      cycle_mem_iff := mem_absorbCycle_iff K hfull }
  decomposition := by
    show K.firstSide ++ K.secondSide ++ K.targetArc.darts =
      K.firstSide ++ invDarts X (emptyArc (cellDarts X k)).darts ++ K.secondSide ++
        K.targetArc.darts
    rw [emptyArc_darts, invDarts_nil, List.append_nil]
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le
  lo_le := K.lo_le
  le_hi := K.le_hi

/-- The absorbed pocket is in walk order. -/
theorem closedWalk_absorbSource (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) (k : Fin X.rCellCount)
    (hk : (cell X k).face ∉ insert (cell X K.source).face K.faces) :
    (absorbSource K hfull k hk).ClosedWalk := by
  obtain ⟨p, hp⟩ := (closed_iff_exists_walk
    (f := fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)) (g := X.toCombMap.vertexOf)
    K.boundary.cycle K.boundary.cycle_nonempty).mp hK
  rw [K.decomposition] at hp
  obtain ⟨r₃, hp₃, h₄⟩ := walk_append_iff.mp hp
  obtain ⟨r₂, hp₂, h₃⟩ := walk_append_iff.mp hp₃
  obtain ⟨r₁, h₁, h₂⟩ := walk_append_iff.mp hp₂
  have h12 : r₁ = r₂ := walk_invDarts_full K hfull h₂
  rw [h12] at h₁
  have hnew : Walk (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)) X.toCombMap.vertexOf p
      (K.firstSide ++ K.secondSide ++ K.targetArc.darts) p :=
    walk_append_iff.mpr ⟨r₃, walk_append_iff.mpr ⟨r₂, h₁, h₃⟩, h₄⟩
  exact (closed_iff_exists_walk
    (f := fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)) (g := X.toCombMap.vertexOf)
    (K.firstSide ++ K.secondSide ++ K.targetArc.darts) (absorbCycle_ne_nil K hfull)).mpr
    ⟨p, hnew⟩

/-- The absorbed pocket has a proper source arc. -/
theorem absorbSource_sourceArc_lt (K : PocketFaceSet D eps X lo hi)
    (hfull : K.sourceArc.length = (cellDarts X K.source).length) (k : Fin X.rCellCount)
    (hk : (cell X k).face ∉ insert (cell X K.source).face K.faces) :
    (absorbSource K hfull k hk).sourceArc.length <
      (cellDarts X (absorbSource K hfull k hk).source).length := by
  show 0 < (cellDarts X k).length
  exact List.length_pos_iff.mpr (X.faceBoundary (cell X k).face).nonempty

end Absorb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.closedWalk_absorbSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.absorbSource_sourceArc_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08
