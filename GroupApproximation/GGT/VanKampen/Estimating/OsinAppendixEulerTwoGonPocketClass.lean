import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonFaceClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The face class of a two-gon of `Φ'_M` in its pocket

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  A two-gon of `phiMapO` with no corner
in its gap bounds a pocket between two exterior regions `a` and `b` of one cell `i`, both with
boundary targets.  This module follows the face class `x` of the two-gon, in the dual of the
collapsed map, through the pocket.

* `ExtPhiData.faceClassO_of_mem_leftSide`, `ExtPhiData.faceClassO_of_mem_rightSide`: the class
  runs along the left side of `a` and the right side of `b`, through darts that are not retained;
* `faceClassO_of_face_not_mem`: it holds every dart of a face outside the regions that it meets;
* `ExtPhiData.false_of_faceClassO_mem_region`: it meets no region other than `a` and `b`;
* `ExtPhiData.twoGonPocketFace_of_faceClassO`: every face it meets, other than the outer face and
  cell `i`, is a `TwoGonPocketFace`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- On a boundary target, the target darts of a region boundary are the target arc. -/
theorem targetBoundaryDarts_eq_darts_of_none (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    (ht : target = none) : targetBoundaryDarts Delta target arc = arc.darts := by
  subst ht
  rfl

namespace RegionCandidate

variable {Delta : DiscDiagram.{u, w, v} W} {family E : Finset (RegionCandidate D eps Delta)}

/-- A midpoint crossing dart of a region with a boundary target is the reverse of a source dart or
the first target dart. -/
theorem mem_reverseDarts_or_head_of_crossO_false (a : RegionCandidate D eps Delta)
    (ht : a.2.target = none) {s : Bool} {v : Delta.toCombMap.Dart}
    (hv : crossO a s false = some v) :
    v ∈ a.2.sourceArc.reverseDarts ∨ a.2.targetArc.darts.head? = some v := by
  cases s with
  | true =>
      rw [crossO_true, cross_false, Option.map_eq_some_iff] at hv
      obtain ⟨p, hp, rfl⟩ := hv
      simp only [cross, if_true] at hp
      refine Or.inl ?_
      simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
      exact ⟨p, List.mem_of_mem_head? hp, rfl⟩
  | false =>
      rw [crossO_false_of_eq_none a ht, Bool.not_false] at hv
      simp only [cross, if_true] at hv
      exact Or.inr hv

/-- **A face class around a face outside the regions** holds every dart of the face once it holds
one, when it retains no dart of the face. -/
theorem faceClassO_of_face_not_mem {x : (collapsedMap family).Dart} {F : Delta.toCombMap.Face}
    (hF : ∀ a ∈ family, F ∉ a.1)
    (hkF : ∀ u, FaceClassO family E x u → Delta.toCombMap.faceOf u.1 = F → ¬ PhiKeepO family E u)
    {z : (collapsedMap family).Dart} (hz : Delta.toCombMap.faceOf z.1 = F)
    (hxz : FaceClassO family E x z) {v : (collapsedMap family).Dart}
    (hv : Delta.toCombMap.faceOf v.1 = F) : FaceClassO family E x v := by
  obtain ⟨n, rfl⟩ := collapsed_exists_pow_of_face_not_mem hF hz hv
  refine (faceClassO_pow_of_invariant (fun u => Delta.toCombMap.faceOf u.1 = F) ?_ hz hxz n).2
  intro u hu hxu
  have hu' : Delta.toCombMap.faceOf u.1 = F := hu
  refine ⟨hkF u hxu hu', ?_⟩
  have h1 := collapsed_pow_val_of_face_not_mem hF 1 hu'
  simp only [pow_one] at h1
  show Delta.toCombMap.faceOf ((collapsedMap family).facePerm u).1 = F
  rw [h1, Delta.toCombMap.faceOf_facePerm, hu']

/-- **The face class of a two-gon meets no other region.**  The retained darts of the class `x` lie
on the outer face, in `a`, on cell `i` or in `b`, and a region whose source cell the class meets
is selected. -/
theorem ExtPhiData.false_of_faceClassO_mem_region (P : ExtPhiData family E)
    {x : (collapsedMap family).Dart} {a b : RegionCandidate D eps Delta} (ha : a ∈ family)
    (hb : b ∈ family) (i : Fin Delta.rCellCount)
    (hkd : ∀ u, FaceClassO family E x u → PhiKeepO family E u →
      Delta.toCombMap.faceOf u.1 = Delta.outerFace ∨ Delta.toCombMap.faceOf u.1 ∈ a.1 ∨
        Delta.toCombMap.faceOf u.1 = (cell Delta i).face ∨ Delta.toCombMap.faceOf u.1 ∈ b.1)
    (hsrc : ∀ u, FaceClassO family E x u → ∀ r ∈ family,
      Delta.toCombMap.faceOf u.1 = (cell Delta r.2.source).face → r ∈ E)
    (hnondeg : ∀ r ∈ family, 0 < r.2.sourceArc.length ∧ 0 < r.2.targetArc.length)
    {r : RegionCandidate D eps Delta} (hr : r ∈ family) (hra : r ≠ a) (hrb : r ≠ b)
    {u : Delta.toCombMap.Dart} (hu₀ : ¬ RegionInternal family u)
    (hxu : FaceClassO family E x ⟨u, hu₀⟩) (hu : Delta.toCombMap.faceOf u ∈ r.1) : False := by
  have hnk : ∀ u' : (collapsedMap family).Dart, FaceClassO family E x u' →
      Delta.toCombMap.faceOf u'.1 ∈ r.1 → ¬ PhiKeepO family E u' := by
    intro u' hxu' hf hk
    rcases hkd u' hxu' hk with h | h | h | h
    · exact (r.2.boundary.all_gCells _ hf).1 h
    · exact hra (eq_of_face_mem_of_face_mem P.pairwise hr ha hf h)
    · exact P.cell_not_mem r hr i (by rw [← h]; exact hf)
    · exact hrb (eq_of_face_mem_of_face_mem P.pairwise hr hb hf h)
  have hS : ∀ u' : (collapsedMap family).Dart, u'.1 ∈ r.2.boundary.cycle →
      FaceClassO family E x u' →
      ¬ PhiKeepO family E u' ∧ ((collapsedMap family).facePerm u').1 ∈ r.2.boundary.cycle := by
    rintro ⟨v, hv⟩ hmem hxv
    refine ⟨hnk _ hxv ((r.2.boundary.cycle_mem_iff v).mp hmem).1, ?_⟩
    obtain ⟨e, he, hstep⟩ := r.2.boundary.exists_boundaryStep_of_mem hmem
    rw [collapsed_facePerm_of_boundaryStep hr hstep hv
      (not_regionInternal_of_mem_cycle P.pairwise hr he)]
    exact he
  have hcyc : u ∈ r.2.boundary.cycle :=
    (r.2.boundary.cycle_mem_iff u).mpr ⟨hu, fun h => hu₀ ⟨r, hr, hu, h⟩⟩
  obtain ⟨p, hp⟩ := exists_crossO r (hnondeg r hr) true true
  have hq : crossO r true false = some (Delta.toCombMap.alpha p) :=
    (crossO_alpha r true true p).mpr hp
  have hqc := mem_cycle_crossO_false r hq
  have hqr := not_regionInternal_of_mem_cycle P.pairwise hr hqc
  obtain ⟨n, hn⟩ := (((collapsedMap family).faceOf_eq_iff _ _).mp
    (collapsed_faceOf_eq_of_mem_cycle P.pairwise hr hcyc hqc)).exists_nat_pow_eq
  have hZq : FaceClassO family E x ⟨Delta.toCombMap.alpha p, hqr⟩ := by
    have h := (faceClassO_pow_of_invariant (fun u' => u'.1 ∈ r.2.boundary.cycle) hS
      (z := ⟨u, hu₀⟩) hcyc hxu n).2
    rwa [hn] at h
  have hkq : ¬ PhiKeepO family E ⟨Delta.toCombMap.alpha p, hqr⟩ :=
    hnk _ hZq (faceOf_crossO_false r hq)
  have hZp : FaceClassO family E x ((collapsedMap family).alpha ⟨Delta.toCombMap.alpha p, hqr⟩) :=
    Relation.EqvGen.trans _ _ _ hZq (Relation.EqvGen.rel _ _ (Or.inr ⟨hkq, rfl⟩))
  have hval : ((collapsedMap family).alpha ⟨Delta.toCombMap.alpha p, hqr⟩).1 = p :=
    ((collapsedMap_isRestriction family).alpha_map ⟨Delta.toCombMap.alpha p, hqr⟩).trans
      (Delta.toCombMap.alpha_involutive p)
  have hpface : Delta.toCombMap.faceOf p = (cell Delta r.2.source).face := faceOf_crossO_true r hp
  have hrE : r ∈ E := hsrc _ hZp r hr (by rw [hval]; exact hpface)
  exact hkq ⟨r, hrE, true, false, hq⟩

/-- **The face class of a two-gon runs along the left side of `a`**, a region with a boundary
target, from the reverse `u₀` of the first target dart of `a`. -/
theorem ExtPhiData.faceClassO_of_mem_leftSide (P : ExtPhiData family E)
    {a : RegionCandidate D eps Delta} (ha : a ∈ family) (ht : a.2.target = none)
    {x u₀ : (collapsedMap family).Dart}
    (hu₀ : a.2.targetArc.darts.head? = some (Delta.toCombMap.alpha u₀.1))
    (hZ : FaceClassO family E x u₀) :
    ∀ v ∈ a.2.leftSide, ∀ hv : ¬ RegionInternal family v,
      FaceClassO family E x ⟨v, hv⟩ ∧ ¬ PhiKeepO family E ⟨v, hv⟩ := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hu₀
  have hc : a.2.boundary.cycle = a.2.sourceArc.reverseDarts ++
      (a.2.rightSide ++ (Delta.toCombMap.alpha u₀.1 :: (ys ++ a.2.leftSide))) := by
    rw [a.2.boundary_decomposition, targetBoundaryDarts_eq_darts_of_none Delta _ _ ht, hys]
    simp only [List.append_assoc, List.cons_append]
  have hnd : (a.2.sourceArc.reverseDarts ++
      (a.2.rightSide ++ (Delta.toCombMap.alpha u₀.1 :: (ys ++ a.2.leftSide)))).Nodup := by
    rw [← hc]
    exact a.2.boundary.cycle_nodup
  have hmem : ∀ w ∈ ys ++ a.2.leftSide, w ∈ a.2.boundary.cycle := by
    intro w hw
    rw [hc]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ hw))
  have hnk : ∀ w ∈ ys ++ a.2.leftSide, ¬ ∃ r ∈ E, ∃ s o : Bool, crossO r s o = some w := by
    intro w hw hk
    obtain ⟨-, s, hs⟩ := P.crossO_false_of_phiKeepO
      (u := ⟨w, not_regionInternal_of_mem_cycle P.pairwise ha (hmem w hw)⟩) hk ha
      ((a.2.boundary.cycle_mem_iff w).mp (hmem w hw)).1
    have hs' : crossO a s false = some w := hs
    rcases mem_reverseDarts_or_head_of_crossO_false a ht hs' with h | h
    · exact List.disjoint_of_nodup_append hnd h
        (List.mem_append_right _ (List.mem_cons_of_mem _ hw))
    · rw [hys, List.head?_cons, Option.some.injEq] at h
      subst h
      exact (List.nodup_cons.mp hnd.of_append_right.of_append_right).1 hw
  have hch : (Delta.toCombMap.alpha u₀.1 :: (ys ++ a.2.leftSide)).IsChain
      (BoundaryStep Delta a.1) := by
    have h := a.2.boundary.cycle_chain
    rw [hc] at h
    exact (h.suffix (List.suffix_append _ _)).suffix (List.suffix_append _ _)
  have hα : ¬ RegionInternal family (Delta.toCombMap.alpha u₀.1) := by
    rw [regionInternal_alpha]
    exact u₀.2
  have hZ1 : FaceClassO family E x
      ((collapsedMap family).facePerm ⟨Delta.toCombMap.alpha u₀.1, hα⟩) := by
    have hcal : (collapsedMap family).alpha u₀ = ⟨Delta.toCombMap.alpha u₀.1, hα⟩ :=
      Subtype.ext ((collapsedMap_isRestriction family).alpha_map u₀)
    rw [← hcal]
    exact Relation.EqvGen.trans _ _ _ hZ (Relation.EqvGen.rel _ _ (Or.inl rfl))
  intro v hv hvr
  have hvl : v ∈ ys ++ a.2.leftSide := List.mem_append_right _ hv
  exact ⟨faceClassO_of_isChain (R := BoundaryStep Delta a.1)
    (fun _ _ h hu hw => collapsed_facePerm_of_boundaryStep ha h hu hw) (ys ++ a.2.leftSide) _ hα
    hZ1 hch (fun w hw => not_regionInternal_of_mem_cycle P.pairwise ha (hmem w hw))
    (fun w hw => hnk w (List.dropLast_subset _ hw)) v hvr hvl, hnk v hvl⟩

/-- **The face class of a two-gon runs along the right side of `b`**, a region with a boundary
target, from the first source dart `u₀` of `b`. -/
theorem ExtPhiData.faceClassO_of_mem_rightSide (P : ExtPhiData family E)
    {b : RegionCandidate D eps Delta} (hb : b ∈ family) (ht : b.2.target = none)
    {x u₀ : (collapsedMap family).Dart} (hu₀ : b.2.sourceArc.darts.head? = some u₀.1)
    (hZ : FaceClassO family E x u₀) :
    ∀ v ∈ b.2.rightSide, ∀ hv : ¬ RegionInternal family v,
      FaceClassO family E x ⟨v, hv⟩ ∧ ¬ PhiKeepO family E ⟨v, hv⟩ := by
  obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.mp hu₀
  have hc0 : b.2.boundary.cycle =
      b.2.sourceArc.reverseDarts ++ (b.2.rightSide ++ (b.2.targetArc.darts ++ b.2.leftSide)) := by
    rw [b.2.boundary_decomposition, targetBoundaryDarts_eq_darts_of_none Delta _ _ ht]
    simp only [List.append_assoc]
  have hnd : (b.2.sourceArc.reverseDarts ++
      (b.2.rightSide ++ (b.2.targetArc.darts ++ b.2.leftSide))).Nodup := by
    rw [← hc0]
    exact b.2.boundary.cycle_nodup
  have hmem : ∀ w ∈ b.2.rightSide, w ∈ b.2.boundary.cycle := by
    intro w hw
    rw [hc0]
    exact List.mem_append_right _ (List.mem_append_left _ hw)
  have hnk : ∀ w ∈ b.2.rightSide, ¬ ∃ r ∈ E, ∃ s o : Bool, crossO r s o = some w := by
    intro w hw hk
    obtain ⟨-, s, hs⟩ := P.crossO_false_of_phiKeepO
      (u := ⟨w, not_regionInternal_of_mem_cycle P.pairwise hb (hmem w hw)⟩) hk hb
      ((b.2.boundary.cycle_mem_iff w).mp (hmem w hw)).1
    have hs' : crossO b s false = some w := hs
    rcases mem_reverseDarts_or_head_of_crossO_false b ht hs' with h | h
    · exact List.disjoint_of_nodup_append hnd h (List.mem_append_left _ hw)
    · exact List.disjoint_of_nodup_append hnd.of_append_right hw
        (List.mem_append_left _ (List.mem_of_mem_head? h))
  have hc : b.2.boundary.cycle = zs.reverse.map Delta.toCombMap.alpha ++
      (Delta.toCombMap.alpha u₀.1 :: (b.2.rightSide ++ (b.2.targetArc.darts ++ b.2.leftSide))) := by
    rw [hc0, CyclicArc.reverseDarts, hzs]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  have hch : (Delta.toCombMap.alpha u₀.1 :: b.2.rightSide).IsChain (BoundaryStep Delta b.1) := by
    have h := b.2.boundary.cycle_chain
    rw [hc] at h
    exact (h.suffix (List.suffix_append _ _)).prefix ⟨b.2.targetArc.darts ++ b.2.leftSide, rfl⟩
  have hα : ¬ RegionInternal family (Delta.toCombMap.alpha u₀.1) := by
    rw [regionInternal_alpha]
    exact u₀.2
  have hZ1 : FaceClassO family E x
      ((collapsedMap family).facePerm ⟨Delta.toCombMap.alpha u₀.1, hα⟩) := by
    have hcal : (collapsedMap family).alpha u₀ = ⟨Delta.toCombMap.alpha u₀.1, hα⟩ :=
      Subtype.ext ((collapsedMap_isRestriction family).alpha_map u₀)
    rw [← hcal]
    exact Relation.EqvGen.trans _ _ _ hZ (Relation.EqvGen.rel _ _ (Or.inl rfl))
  intro v hv hvr
  exact ⟨faceClassO_of_isChain (R := BoundaryStep Delta b.1)
    (fun _ _ h hu hw => collapsed_facePerm_of_boundaryStep hb h hu hw) b.2.rightSide _ hα
    hZ1 hch (fun w hw => not_regionInternal_of_mem_cycle P.pairwise hb (hmem w hw))
    (fun w hw => hnk w (List.dropLast_subset _ hw)) v hvr hv, hnk v hv⟩

/-- **A face of the pocket of a two-gon** between `a` and `b`: a face of `a` or of `b`, or a face
outside the regions all of whose darts lie in the face class `x`. -/
def TwoGonPocketFace (family E : Finset (RegionCandidate D eps Delta))
    (x : (collapsedMap family).Dart) (a b : RegionCandidate D eps Delta)
    (F : Delta.toCombMap.Face) : Prop :=
  F ∈ a.1 ∨ F ∈ b.1 ∨ ((∀ r ∈ family, F ∉ r.1) ∧
    ∀ v : (collapsedMap family).Dart, Delta.toCombMap.faceOf v.1 = F → FaceClassO family E x v)

/-- **Every face that the face class of a two-gon meets**, other than the outer face and cell `i`,
is a face of its pocket. -/
theorem ExtPhiData.twoGonPocketFace_of_faceClassO (P : ExtPhiData family E)
    {x : (collapsedMap family).Dart} {a b : RegionCandidate D eps Delta} (ha : a ∈ family)
    (hb : b ∈ family) (i : Fin Delta.rCellCount)
    (hkd : ∀ u, FaceClassO family E x u → PhiKeepO family E u →
      Delta.toCombMap.faceOf u.1 = Delta.outerFace ∨ Delta.toCombMap.faceOf u.1 ∈ a.1 ∨
        Delta.toCombMap.faceOf u.1 = (cell Delta i).face ∨ Delta.toCombMap.faceOf u.1 ∈ b.1)
    (hsrc : ∀ u, FaceClassO family E x u → ∀ r ∈ family,
      Delta.toCombMap.faceOf u.1 = (cell Delta r.2.source).face → r ∈ E)
    (hnondeg : ∀ r ∈ family, 0 < r.2.sourceArc.length ∧ 0 < r.2.targetArc.length)
    {v : (collapsedMap family).Dart} (hxv : FaceClassO family E x v)
    (hout : Delta.toCombMap.faceOf v.1 ≠ Delta.outerFace)
    (hcell : Delta.toCombMap.faceOf v.1 ≠ (cell Delta i).face) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf v.1) := by
  by_cases hF : ∀ r ∈ family, Delta.toCombMap.faceOf v.1 ∉ r.1
  · have hkF : ∀ u, FaceClassO family E x u →
        Delta.toCombMap.faceOf u.1 = Delta.toCombMap.faceOf v.1 → ¬ PhiKeepO family E u := by
      intro u hxu hu hk
      rcases hkd u hxu hk with h | h | h | h
      · exact hout (hu.symm.trans h)
      · exact hF a ha (by rw [← hu]; exact h)
      · exact hcell (hu.symm.trans h)
      · exact hF b hb (by rw [← hu]; exact h)
    exact Or.inr (Or.inr ⟨hF, fun v' hv' => faceClassO_of_face_not_mem hF hkF rfl hxv hv'⟩)
  · push_neg at hF
    obtain ⟨r, hr, hfr⟩ := hF
    by_cases hra : r = a
    · exact Or.inl (by subst hra; exact hfr)
    by_cases hrb : r = b
    · exact Or.inr (Or.inl (by subst hrb; exact hfr))
    exact (P.false_of_faceClassO_mem_region ha hb i hkd hsrc hnondeg hr hra hrb v.2 hxv hfr).elim

end RegionCandidate

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.targetBoundaryDarts_eq_darts_of_none
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_reverseDarts_or_head_of_crossO_false
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceClassO_of_face_not_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.false_of_faceClassO_mem_region
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.faceClassO_of_mem_leftSide
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.faceClassO_of_mem_rightSide
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_of_faceClassO
