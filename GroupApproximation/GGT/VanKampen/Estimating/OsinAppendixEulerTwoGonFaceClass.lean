import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonLabels
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSmallFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Face classes of a two-gon of `Φ'_M`

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  `TwoGonHoldsInput`
(`Estimating/OsinAppendixEulerSmallFaces.lean`) asks that a two-gon of `phiMapO` with no corner in
its gap holds a relator cell.  The proof follows the face class of the two-gon in the dual of the
collapsed map around the pocket between its two regions.  This module collects the tools.

* `ExtPhiData.faceOf_of_faceClassO_twoGon`: a retained dart in the face class of a two-gon lies on
  the outer face, in one of its two regions, or on the source cell;
* `faceClassO_pow_of_invariant`, `faceClassO_of_isChain`: a face class runs around a face of the
  collapsed map, and along a chain of face rotations, through darts that are not retained;
* `collapsed_exists_pow_of_face_not_mem`: around a face outside the regions, the collapsed map
  turns as the diagram does;
* `CyclicArc.darts_prefix_of_start_eq`, `CyclicArc.mem_darts_of_le`: inclusions of arcs.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v

/-- Two arcs from one start: the shorter is a prefix of the longer. -/
theorem CyclicArc.darts_prefix_of_start_eq {α : Type*} {cycle : List α} (X Y : CyclicArc cycle)
    (hs : X.start.1 = Y.start.1) (hl : X.length ≤ Y.length) : X.darts <+: Y.darts := by
  have hr : X.rotated = Y.rotated := by simp only [CyclicArc.rotated, hs]
  show X.rotated.take X.length <+: Y.rotated.take Y.length
  rw [hr]
  exact List.take_prefix_take_left hl

/-- An arc between the ends of an arc that does not wrap around lies in it. -/
theorem CyclicArc.mem_darts_of_le {α : Type*} {cycle : List α} (X Y : CyclicArc cycle)
    (hs : Y.start.1 ≤ X.start.1) (he : X.start.1 + X.length ≤ Y.start.1 + Y.length)
    (hY : Y.start.1 + Y.length ≤ cycle.length) {d : α} (hd : d ∈ X.darts) : d ∈ Y.darts := by
  have hlen : Y.length ≤ (cycle.drop Y.start.1).length := by
    rw [List.length_drop]
    omega
  rw [CyclicArc.darts, CyclicArc.rotated, List.take_append_of_le_length hlen]
  have h := X.mem_drop_take_of_le hs he hY hd
  rwa [Nat.add_sub_cancel_left] at h

namespace RegionCandidate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- The orbit of a point of period four. -/
theorem twoGon_pow_cases {α : Type*} (σ : Equiv.Perm α) {y : α} (h4 : σ (σ (σ (σ y))) = y)
    (n : ℕ) :
    (σ ^ n) y = y ∨ (σ ^ n) y = σ y ∨ (σ ^ n) y = σ (σ y) ∨ (σ ^ n) y = σ (σ (σ y)) := by
  induction n with
  | zero => exact Or.inl (by rw [pow_zero, Equiv.Perm.one_apply])
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h | h | h <;> rw [h]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl h4

variable {Delta : DiscDiagram.{u, w, v} W} {family E : Finset (RegionCandidate D eps Delta)}

/-- One step around a face from a cell dart reaches a midpoint dart. -/
theorem ExtPhiData.phiCellSideO_facePerm (P : ExtPhiData family E) (x : (phiMapO family E).Dart)
    (hx : phiCellSideO x = true) : phiCellSideO ((phiMapO family E).facePerm x) = false := by
  obtain ⟨-, -, hc1⟩ := P.phiO_alpha x
  have hc1' : phiCellSideO ((phiMapO family E).alpha x) = false := by simp [hc1, hx]
  exact (P.phiCellSideO_sigma ((phiMapO family E).alpha x)).trans hc1'

/-- **The retained darts in the face class of a two-gon.**  They lie on the outer face, in the
region of the outer cell dart `y`, on its source cell, or in the region two steps on. -/
theorem ExtPhiData.faceOf_of_faceClassO_twoGon (P : ExtPhiData family E)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesEndO E) a b)
    {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (hnone : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    {z : (phiMapO family E).Dart} (hyz : FaceClassO family E y.1 z.1) :
    Delta.toCombMap.faceOf z.1.1 = endFace Delta none ∨ Delta.toCombMap.faceOf z.1.1 ∈ (phiRegionO y).1 ∨
      Delta.toCombMap.faceOf z.1.1 = endFace Delta (some (phiRegionO y).2.source) ∨
      Delta.toCombMap.faceOf z.1.1 ∈
        (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))).1 := by
  have hs' : sideCellO (phiRegionO y) (!phiSideO y) = some (phiRegionO y).2.source := by
    cases hs : phiSideO y
    · rfl
    · simp [hs, sideCellO] at hnone
  have hc2 := (sideCellO_facePerm_facePerm P y hy).1
  obtain ⟨n, hn⟩ := (((phiMapO family E).faceOf_eq_iff y z).mp
    (faceOf_eq_of_faceClassO P hlinked hyz)).exists_nat_pow_eq
  rcases twoGon_pow_cases _ h4 n with h | h | h | h <;> rw [h] at hn <;> subst hn
  · have hc := phiO_cross y
    rw [hy] at hc
    exact Or.inl ((faceOf_crossO_true _ hc).trans (by rw [hnone]))
  · have hc := phiO_cross ((phiMapO family E).facePerm y)
    rw [P.phiCellSideO_facePerm y hy, P.phiRegionO_facePerm y hy] at hc
    exact Or.inr (Or.inl (faceOf_crossO_false _ hc))
  · have hc := phiO_cross ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))
    rw [hc2] at hc
    refine Or.inr (Or.inr (Or.inl ((faceOf_crossO_true _ hc).trans ?_)))
    rw [(sideCellO_facePerm_facePerm P y hy).2, hs']
  · have hc := phiO_cross ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
    rw [P.phiCellSideO_facePerm _ hc2, P.phiRegionO_facePerm _ hc2] at hc
    exact Or.inr (Or.inr (Or.inr (faceOf_crossO_false _ hc)))

/-- A retained dart based inside a region of the family is a midpoint dart of that region. -/
theorem ExtPhiData.crossO_false_of_phiKeepO (P : ExtPhiData family E)
    {u : (collapsedMap family).Dart} (hu : PhiKeepO family E u) {r : RegionCandidate D eps Delta}
    (hr : r ∈ family) (hf : Delta.toCombMap.faceOf u.1 ∈ r.1) :
    r ∈ E ∧ ∃ s, crossO r s false = some u.1 := by
  obtain ⟨a, ha, s, o, h⟩ := hu
  cases o with
  | true => exact absurd hf (P.face_not_mem_of_crossO_true h r hr)
  | false =>
      have hra : a = r :=
        eq_of_face_mem_of_face_mem P.pairwise (P.subset ha) hr (faceOf_crossO_false a h) hf
      subst hra
      exact ⟨ha, s, h⟩

/-- **A face class runs around a face of the collapsed map** along an invariant through darts
that are not retained. -/
theorem faceClassO_pow_of_invariant {x : (collapsedMap family).Dart}
    (S : (collapsedMap family).Dart → Prop)
    (hS : ∀ u, S u → FaceClassO family E x u →
      ¬ PhiKeepO family E u ∧ S ((collapsedMap family).facePerm u))
    {z : (collapsedMap family).Dart} (hz : S z) (hxz : FaceClassO family E x z) (n : ℕ) :
    S (((collapsedMap family).facePerm ^ n) z) ∧
      FaceClassO family E x (((collapsedMap family).facePerm ^ n) z) := by
  induction n with
  | zero =>
      simp only [pow_zero, Equiv.Perm.one_apply]
      exact ⟨hz, hxz⟩
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      obtain ⟨hk, hS'⟩ := hS _ ih.1 ih.2
      exact ⟨hS', Relation.EqvGen.trans _ _ _ ih.2
        (eqvGen_facePerm_of_not_keep (M := collapsedMap family) (keep := PhiKeepO family E) hk)⟩

/-- A face class holds the reverse of a dart exactly when it holds its face rotation. -/
theorem faceClassO_alpha_iff {x u : (collapsedMap family).Dart} :
    FaceClassO family E x ((collapsedMap family).alpha u) ↔
      FaceClassO family E x ((collapsedMap family).facePerm u) := by
  have h : FaceClassO family E ((collapsedMap family).alpha u)
      ((collapsedMap family).facePerm u) :=
    eqvGen_sigma_of_alpha (M := collapsedMap family) (keep := PhiKeepO family E) u
  exact ⟨fun hx => Relation.EqvGen.trans _ _ _ hx h,
    fun hx => Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ h)⟩

/-- Around a face outside the regions, the collapsed map turns as the diagram does. -/
theorem collapsed_pow_val_of_face_not_mem {F : Delta.toCombMap.Face}
    (hF : ∀ a ∈ family, F ∉ a.1) (n : ℕ) {z : (collapsedMap family).Dart}
    (hz : Delta.toCombMap.faceOf z.1 = F) :
    (((collapsedMap family).facePerm ^ n) z).1 = (Delta.toCombMap.facePerm ^ n) z.1 := by
  induction n generalizing z with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]
  | succ n ih =>
      have hface : ∀ a ∈ family, Delta.toCombMap.faceOf z.1 ∉ a.1 := by
        intro a ha
        rw [hz]
        exact hF a ha
      have hy : ((collapsedMap family).facePerm z).1 = Delta.toCombMap.facePerm z.1 :=
        congrArg Subtype.val (collapsed_facePerm_of_face_not_mem hface)
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply,
        ih (z := (collapsedMap family).facePerm z)
          (by rw [hy, Delta.toCombMap.faceOf_facePerm, hz]), hy]

/-- **The darts of the collapsed map on a face outside the regions** lie on one face cycle. -/
theorem collapsed_exists_pow_of_face_not_mem {F : Delta.toCombMap.Face}
    (hF : ∀ a ∈ family, F ∉ a.1) {z x : (collapsedMap family).Dart}
    (hz : Delta.toCombMap.faceOf z.1 = F) (hx : Delta.toCombMap.faceOf x.1 = F) :
    ∃ n : ℕ, ((collapsedMap family).facePerm ^ n) z = x := by
  obtain ⟨n, hn⟩ :=
    ((Delta.toCombMap.faceOf_eq_iff z.1 x.1).mp (hz.trans hx.symm)).exists_nat_pow_eq
  exact ⟨n, Subtype.ext ((collapsed_pow_val_of_face_not_mem hF n hz).trans hn)⟩

/-- **A face class runs along a chain of face rotations** of the collapsed map, through darts
that are not retained: it holds every dart of the chain after the first. -/
theorem faceClassO_of_isChain {R : Delta.toCombMap.Dart → Delta.toCombMap.Dart → Prop}
    (hR : ∀ u v, R u v → ∀ (hu : ¬ RegionInternal family u) (hv : ¬ RegionInternal family v),
      (collapsedMap family).facePerm ⟨u, hu⟩ = ⟨v, hv⟩)
    {x : (collapsedMap family).Dart} (l : List Delta.toCombMap.Dart) :
    ∀ (x₀ : Delta.toCombMap.Dart) (hx₀ : ¬ RegionInternal family x₀),
      FaceClassO family E x ((collapsedMap family).facePerm ⟨x₀, hx₀⟩) →
      (x₀ :: l).IsChain R → (∀ v ∈ l, ¬ RegionInternal family v) →
      (∀ v ∈ l.dropLast, ¬ ∃ b ∈ E, ∃ s o : Bool, crossO b s o = some v) →
      ∀ v (hv : ¬ RegionInternal family v), v ∈ l → FaceClassO family E x ⟨v, hv⟩ := by
  induction l with
  | nil =>
      intro _ _ _ _ _ _ _ _ hmem
      simp at hmem
  | cons v₁ l ih =>
      intro x₀ hx₀ hcls hchain hint hkeep v hv hmem
      obtain ⟨hr, hchain'⟩ := List.isChain_cons_cons.mp hchain
      have hv₁ : ¬ RegionInternal family v₁ := hint v₁ List.mem_cons_self
      have h1 : FaceClassO family E x ⟨v₁, hv₁⟩ := by
        rw [← hR x₀ v₁ hr hx₀ hv₁]
        exact hcls
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact h1
      · have hl : l ≠ [] := List.ne_nil_of_mem hmem'
        have hk : ¬ ∃ b ∈ E, ∃ s o : Bool, crossO b s o = some v₁ := by
          apply hkeep v₁
          rw [List.dropLast_cons_of_ne_nil hl]
          exact List.mem_cons_self
        refine ih v₁ hv₁ ?_ hchain' (fun w hw => hint w (List.mem_cons_of_mem _ hw)) ?_ v hv hmem'
        · exact Relation.EqvGen.trans _ _ _ h1
            (eqvGen_facePerm_of_not_keep (M := collapsedMap family) (keep := PhiKeepO family E)
              (x := ⟨v₁, hv₁⟩) hk)
        · intro w hw
          apply hkeep w
          rw [List.dropLast_cons_of_ne_nil hl]
          exact List.mem_cons_of_mem _ hw

end RegionCandidate

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.darts_prefix_of_start_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.mem_darts_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGon_pow_cases
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.phiCellSideO_facePerm
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.faceOf_of_faceClassO_twoGon
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.crossO_false_of_phiKeepO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceClassO_pow_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceClassO_alpha_iff
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_pow_val_of_face_not_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_exists_pow_of_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceClassO_of_isChain
