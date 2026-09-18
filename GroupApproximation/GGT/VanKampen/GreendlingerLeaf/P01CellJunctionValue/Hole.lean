import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Pocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Case B: the hole behind the corner

With the outer dart reached from `facePerm a` in the joined map, the darts `b, …, a` of the cell
`C` after the gap form a closed face walk `seg b (n + 1)`, closing by a first turn from `a` to `b`
around the corner vertex.  Its enclosed faces hold the polygon face `f = faceOf (α b)`, not `C`,
not the outer face, and no relator cell; and a dart on an enclosed face whose reverse is not on
`C` has its reverse on an enclosed face (`HoleRegion`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

theorem pow_apply_pow_apply {α : Type*} (p : Perm α) (x : α) (i j : ℕ) :
    (p ^ i) ((p ^ j) x) = (p ^ (i + j)) x := by
  rw [pow_add, Perm.mul_apply]

/-- Every point returns to itself after some positive number of steps past its image. -/
theorem exists_pos_pow_apply_eq {M : CombMap.{v}} (p : Perm M.Dart) (x : M.Dart) :
    ∃ K, 0 < K ∧ (p ^ K) (p x) = x := by
  have hpos : 0 < orderOf p := orderOf_pos p
  refine ⟨orderOf p * 2 - 1, by omega, ?_⟩
  rw [← pow_succ_apply', Nat.sub_add_cancel (show 1 ≤ orderOf p * 2 by omega), pow_mul,
    pow_orderOf_eq_one, one_pow, Perm.one_apply]

section Walk

variable {M : CombMap.{v}}

/-- The hole walk `b, …, a` is nodup. -/
theorem hole_nodup {a b : M.Dart} {n : ℕ} (hn : (M.facePerm ^ n) b = a)
    (hnleast : ∀ r < n, (M.facePerm ^ r) b ≠ a) : (seg M b (n + 1)).Nodup := by
  refine seg_nodup fun r hr0 hrn h => ?_
  apply hnleast (n - r) (by omega)
  rw [← pow_add_apply_of_fix h (n - r), Nat.sub_add_cancel (show r ≤ n by omega)]
  exact hn

/-- Every dart of the hole walk is reached from `b` in the joined map. -/
theorem hole_reach (hM : M.IsPlanar) {a b : M.Dart} {m n : ℕ} (hm : m ≠ 0)
    (hb : M.sigma b = M.alpha a) (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hnleast : ∀ r < n, (M.facePerm ^ r) b ≠ a) :
    ∀ r ≤ n, Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent b
      ((M.facePerm ^ r) b) := by
  intro r
  induction r with
  | zero =>
    intro _
    rw [pow_zero, Perm.one_apply]
    exact .refl _
  | succ r ih =>
    intro hr
    have ih' := ih (by omega)
    have hne_a : (M.facePerm ^ r) b ≠ a := hnleast r (by omega)
    have hne_p : (M.facePerm ^ r) b ≠ (M.facePerm ^ m) a := by
      intro h
      apply JunctionPocket.junction_not_reach hM hm hb hab hleast
      have hp := JunctionPocket.reach_gap hab hleast (show m - 1 < m by omega)
      rw [Nat.sub_add_cancel (show 1 ≤ m by omega)] at hp
      rw [h] at ih'
      exact .trans _ _ _ ih' (.symm _ _ hp)
    rw [pow_succ_apply]
    exact .trans _ _ _ ih' (JunctionPocket.joined_reach_facePerm hne_p hne_a)

/-- The darts strictly between `α a` and `b` in the rotation are reached from `facePerm a`. -/
theorem hole_turn_reach {a b : M.Dart} {m K : ℕ}
    (hab : (M.facePerm ^ (m + 1)) a = b) (hK : (M.sigma ^ K) (M.alpha a) = b)
    (hKleast : ∀ t, 0 < t → t < K → (M.sigma ^ t) (M.alpha a) ≠ b) :
    ∀ t, 0 < t → t < K → Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent
      (M.facePerm a) ((M.sigma ^ t) (M.alpha a)) := by
  intro t
  induction t with
  | zero =>
    intro h _
    omega
  | succ t ih =>
    intro _ htK
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [pow_succ_apply, pow_zero, Perm.one_apply]
      exact .refl _
    · have ih' := ih ht0 (by omega)
      have hne_a : (M.sigma ^ t) (M.alpha a) ≠ M.alpha a := by
        intro h
        apply hKleast (K - t) (by omega) (by omega)
        rw [← pow_add_apply_of_fix h (K - t), Nat.sub_add_cancel (show t ≤ K by omega)]
        exact hK
      have hne_p : (M.sigma ^ t) (M.alpha a) ≠ M.alpha ((M.facePerm ^ m) a) := by
        intro h
        apply hKleast (t + 1) (by omega) htK
        rw [pow_succ_apply, h]
        exact JunctionPocket.facePerm_last hab
      rw [pow_succ_apply, ← JunctionPocket.joined_sigma_apply_of_ne hne_p hne_a]
      exact .trans _ _ _ ih' (.rel _ _ (Or.inr rfl))

/-- **The hole walk closes** by a first turn from `a` to `b`. -/
theorem hole_firstTurn (hM : M.IsPlanar) {a b : M.Dart} {m n K : ℕ}
    (hm : m ≠ 0) (hb : M.sigma b = M.alpha a) (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hnleast : ∀ r < n, (M.facePerm ^ r) b ≠ a)
    (hK0 : 0 < K) (hK : (M.sigma ^ K) (M.alpha a) = b)
    (hKleast : ∀ t, 0 < t → t < K → (M.sigma ^ t) (M.alpha a) ≠ b) :
    FirstTurn M (seg M b (n + 1)) a b := by
  refine ⟨K, hK0, hK, fun t ht htK hkeep => ?_⟩
  have hreach := hole_turn_reach (m := m) hab hK hKleast t ht htK
  have hall : ∀ y ∈ seg M b (n + 1),
      Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent b y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := mem_seg.mp hy
    exact hole_reach hM hm hb hab hleast hnleast r (by omega)
  apply JunctionPocket.junction_not_reach hM hm hb hab hleast
  rcases hkeep with h | h
  · exact .trans _ _ _ (hall _ h) (.symm _ _ hreach)
  · have hα : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent
        (M.alpha ((M.sigma ^ t) (M.alpha a))) ((M.sigma ^ t) (M.alpha a)) :=
      .rel _ _ (Or.inl (M.alpha_involutive _))
    exact .trans _ _ _ (.trans _ _ _ (hall _ h) hα) (.symm _ _ hreach)

end Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A hole region**: a face set holding `f`, not `C`, not the outer face, no relator cell, and
closed under reversal off `C`. -/
def HoleRegion (X : DiscDiagram.{u, w, v} W) (f C : X.toCombMap.Face)
    (E : Finset X.toCombMap.Face) : Prop :=
  f ∈ E ∧ C ∉ E ∧ X.outerFace ∉ E ∧ (∀ C' ∈ X.relatorCells, C'.face ∉ E) ∧
    ∀ y, X.toCombMap.faceOf y ∈ E → X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ C →
      X.toCombMap.faceOf (X.toCombMap.alpha y) ∈ E

/-- **Case B gives a hole region.** -/
theorem exists_holeRegion (X : DiscDiagram.{u, w, v} W) (hNo : NoCellInside X)
    {a b o : X.toCombMap.Dart} {m : ℕ} (hm : m ≠ 0)
    (hb : X.toCombMap.sigma b = X.toCombMap.alpha a)
    (hab : (X.toCombMap.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (X.toCombMap.facePerm ^ (t + 1)) a ≠ b)
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha b) ≠ X.toCombMap.faceOf a)
    (j : Fin X.rCellCount) (ha : a ∈ cellDarts X j) (ho : X.toCombMap.faceOf o = X.outerFace)
    (hJ : Relation.EqvGen (FoldMap.joined X.toCombMap ((X.toCombMap.facePerm ^ m) a) a).Adjacent
      (X.toCombMap.facePerm a) o) :
    ∃ E, HoleRegion X (X.toCombMap.faceOf (X.toCombMap.alpha b)) (cell X j).face E := by
  have hCa : X.toCombMap.faceOf a = (cell X j).face :=
    ((X.faceBoundary (cell X j).face).mem_iff a).mp ha
  have hba : X.toCombMap.faceOf b = X.toCombMap.faceOf a := by
    rw [← hab, JunctionPocket.faceOf_pow_apply]
  have hexn : ∃ n, (X.toCombMap.facePerm ^ n) b = a := by
    have hpos : 0 < orderOf X.toCombMap.facePerm := orderOf_pos _
    obtain ⟨o', ho'⟩ : ∃ o', orderOf X.toCombMap.facePerm = o' + 1 :=
      ⟨orderOf X.toCombMap.facePerm - 1, by omega⟩
    refine ⟨o' * (m + 1), ?_⟩
    rw [← hab, pow_apply_pow_apply,
      show o' * (m + 1) + (m + 1) = orderOf X.toCombMap.facePerm * (m + 1) by rw [ho']; ring]
    exact pow_orderOf_apply _ _ _
  obtain ⟨n, hn, hnleast⟩ : ∃ n, (X.toCombMap.facePerm ^ n) b = a ∧
      ∀ r < n, (X.toCombMap.facePerm ^ r) b ≠ a :=
    ⟨Nat.find hexn, Nat.find_spec hexn, fun r hr => Nat.find_min hexn hr⟩
  have hexK : ∃ K, 0 < K ∧ (X.toCombMap.sigma ^ K) (X.toCombMap.alpha a) = b := by
    obtain ⟨K, hK0, hK⟩ := exists_pos_pow_apply_eq X.toCombMap.sigma b
    refine ⟨K, hK0, ?_⟩
    rw [← hb]
    exact hK
  obtain ⟨K, ⟨hK0, hK⟩, hKleast⟩ : ∃ K, (0 < K ∧ (X.toCombMap.sigma ^ K) (X.toCombMap.alpha a) = b)
      ∧ ∀ t, 0 < t → t < K → (X.toCombMap.sigma ^ t) (X.toCombMap.alpha a) ≠ b :=
    ⟨Nat.find hexK, Nat.find_spec hexK, fun t ht htK h => Nat.find_min hexK htK ⟨ht, h⟩⟩
  have hc : seg X.toCombMap b (n + 1) ≠ [] := seg_ne_nil (M := X.toCombMap) (x := b)
    (Nat.add_one_ne_zero n)
  have hclose : FirstTurn X.toCombMap (seg X.toCombMap b (n + 1))
      ((seg X.toCombMap b (n + 1)).getLast hc) ((seg X.toCombMap b (n + 1)).head hc) := by
    rw [seg_getLast (Nat.add_one_ne_zero n), Nat.add_sub_cancel, hn,
      seg_head (Nat.add_one_ne_zero n)]
    exact hole_firstTurn X.planar hm hb hab hleast hnleast hK0 hK hKleast
  have hbmem : b ∈ seg X.toCombMap b (n + 1) :=
    mem_seg.mpr ⟨0, by omega, by rw [pow_zero, Perm.one_apply]⟩
  have hcface : ∀ y ∈ seg X.toCombMap b (n + 1), X.toCombMap.faceOf y = (cell X j).face :=
    fun y hy => (faceOf_of_mem_seg hy).trans (hba.trans hCa)
  have hCnot : (cell X j).face ∉ enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)) := by
    have h := faceOf_not_mem_of_chain X.planar hc (seg_isChain _ _) hclose hbmem
    rwa [hcface b hbmem] at h
  have hpnot : X.toCombMap.faceOf ((X.toCombMap.facePerm ^ m) a) ∉
      enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)) := by
    rw [JunctionPocket.faceOf_pow_apply, hCa]
    exact hCnot
  have hanot : X.toCombMap.faceOf a ∉ enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)) := by
    rw [hCa]
    exact hCnot
  have hall : ∀ y ∈ seg X.toCombMap b (n + 1),
      Relation.EqvGen (FoldMap.joined X.toCombMap ((X.toCombMap.facePerm ^ m) a) a).Adjacent
        b y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := mem_seg.mp hy
    exact hole_reach X.planar hm hb hab hleast hnleast r (by omega)
  have hout : X.outerFace ∉ enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)) := by
    intro hout
    have hseed := seed_of_reach (c := seg X.toCombMap b (n + 1))
      (p := (X.toCombMap.facePerm ^ m) a) (a := a) (r := b) hall
    have hreach := reach_of_enclosed hpnot hanot hseed (x := o) (by rw [ho]; exact hout)
    exact JunctionPocket.junction_not_reach X.planar hm hb hab hleast
      (.trans _ _ _ hreach (.symm _ _ hJ))
  have hE := enclosedFaceSetSucc_of_chain X hc (hole_nodup hn hnleast) (seg_isChain _ _) hclose
    hout
  have hsub : seg X.toCombMap b (n + 1) ⊆ cellDarts X j := fun y hy =>
    ((X.faceBoundary (cell X j).face).mem_iff y).mpr (hcface y hy)
  have hlen := ((hole_nodup hn hnleast).subperm hsub).length_le
  rw [length_seg] at hlen
  obtain ⟨A, hA⟩ := CyclicArc.exists_darts_eq_map_pow X j (hsub _ hbmem) hlen
  have hcells := hNo _ _ hE j hCnot A hA
  have hf : X.toCombMap.faceOf (X.toCombMap.alpha b) ∈
      enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)) :=
    faceOf_alpha_mem_of_seed hbmem fun h => hface ((hcface _ h).trans hCa.symm)
  refine ⟨enclosedFaces X.toCombMap (seg X.toCombMap b (n + 1)), hf, hCnot, hout, hcells,
    fun y hy hyC => ?_⟩
  refine faceOf_alpha_mem_enclosedFaces ?_ hy
  rintro (h | h)
  · rw [hcface y h] at hy
    exact hCnot hy
  · exact hyC (hcface _ h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.pow_apply_pow_apply
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.exists_pos_pow_apply_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.hole_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.hole_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.hole_turn_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.hole_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.HoleRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.exists_holeRegion
