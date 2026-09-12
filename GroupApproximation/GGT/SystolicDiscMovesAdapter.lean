import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.GGT.SystolicDiscMovesCycle
import GroupApproximation.GGT.VanKampen.OneFaceWordTrivial
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Triangulated discs and cycle discs, and the pendant constructor (HC3(c))

A triangulated disc (`TriangulatedDisc X γ`) reads its boundary from a base dart by
powers of the face rotation.  A cycle disc (`CycleDisc X`) carries the exterior face as an
explicit face cycle.  The two forms carry the same data:

* `CycleDisc.toTriangulatedDisc`: a cycle disc is a triangulated disc bounding its walk;
* `CycleDisc.exists_of_triangulatedDisc`: every triangulated disc has a cycle form with
  the same boundary.

The boundary lists agree through `ofFn_pow_eq_map_orbitWalk`.  With the list split
`split_boundary`, the pendant move on cycle discs proves `attachPendantStatement`.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- The boundary list of powers of a permutation is the map of an orbit walk. -/
theorem ofFn_pow_eq_map_orbitWalk {D : Type*} {W : Type*} (p : Equiv.Perm D) (g : D → W) :
    ∀ (n : ℕ) (x : D),
      List.ofFn (fun k : Fin n => g ((p ^ (k : ℕ)) x)) = (orbitWalk p x n).map g
  | 0, _ => rfl
  | n + 1, x => by
      rw [List.ofFn_succ, orbitWalk_succ, List.map_cons, ← ofFn_pow_eq_map_orbitWalk p g n (p x)]
      congr 1

/-- A face cycle returns to its head after its length. -/
theorem isFaceCycle_pow_length {M : CombMap.{0}} {l : List M.Dart} (hl : M.IsFaceCycle l) :
    l = orbitWalk M.facePerm (l.head hl.ne_nil) l.length ∧
      (M.facePerm ^ l.length) (l.head hl.ne_nil) = l.head hl.ne_nil := by
  have hwalk := eq_orbitWalk_of_isChain M.facePerm l (l.head hl.ne_nil) hl.chain
    (List.head?_eq_some_head hl.ne_nil)
  refine ⟨hwalk, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 :=
    ⟨l.length - 1, by have := List.length_pos_iff_ne_nil.mpr hl.ne_nil; omega⟩
  have hc := hl.closes
  have hne : orbitWalk M.facePerm (l.head hl.ne_nil) (m + 1) ≠ [] := by simp [orbitWalk_succ]
  rw [List.getLast_congr hl.ne_nil hne (hwalk.trans (by rw [hm])), getLast_orbitWalk] at hc
  rw [hm, pow_succ', Equiv.Perm.mul_apply, hc]

/-- The boundary walk of a face cycle, read by powers from its head. -/
theorem ofFn_boundary_eq {M : CombMap.{0}} {l : List M.Dart} (hl : M.IsFaceCycle l) (g : M.Dart → V) :
    List.ofFn (fun k : Fin (l.length + 1) => g ((M.facePerm ^ (k : ℕ)) (l.head hl.ne_nil))) =
      l.map g ++ [g (l.head hl.ne_nil)] := by
  obtain ⟨hwalk, hper⟩ := isFaceCycle_pow_length hl
  rw [ofFn_pow_eq_map_orbitWalk, orbitWalk_succ', List.map_append, ← hwalk, hper]
  rfl

namespace CycleDisc

/-- **A cycle disc is a triangulated disc bounding its walk.** -/
noncomputable def toTriangulatedDisc (D : CycleDisc X) : TriangulatedDisc X D.boundary where
  map := D.map
  planar := D.planar
  outer := D.map.faceOf (D.cyc.head D.isFaceCycle.ne_nil)
  vtx := Quotient.lift D.lab (fun _ _ h => OrbitClassifier.eq_of_sameCycle D.map.sigma D.lab
    D.lab_sigma h)
  adj d := D.adj d
  tri d hd := D.tri d (fun hm => hd ((D.isFaceCycle.mem_iff d).mp hm))
  base := D.cyc.head D.isFaceCycle.ne_nil
  base_outer := rfl
  boundary := by
    have hdeg : D.map.faceDegree (D.map.faceOf (D.cyc.head D.isFaceCycle.ne_nil)) =
        D.cyc.length := D.isFaceCycle.length_eq.symm
    rw [hdeg]
    exact ofFn_boundary_eq D.isFaceCycle D.lab

/-- **Every triangulated disc has a cycle form with the same boundary.** -/
theorem exists_of_triangulatedDisc {γ : List V} (T : TriangulatedDisc X γ) :
    ∃ D : CycleDisc X, D.boundary = γ := by
  classical
  let B := FaceBoundary.based T.map T.base
  have hbase : T.base ∈ B.darts := (B.mem_iff T.base).mpr rfl
  obtain ⟨k, rest, _, hrot⟩ := B.isFaceCycle.exists_rotate_cons hbase
  have hcyc : T.map.IsFaceCycle (T.base :: rest) := by
    have h := B.isFaceCycle.rotate k
    rwa [hrot] at h
  let D : CycleDisc X :=
    { map := T.map
      planar := T.planar
      lab := fun d => T.vtx (T.map.vertexOf d)
      lab_sigma := fun d => by rw [T.map.vertexOf_sigma]
      adj := T.adj
      cyc := T.base :: rest
      isFaceCycle := hcyc
      tri := fun d hd => T.tri d (fun hface => hd ((hcyc.mem_iff d).mpr
        (by rw [List.head_cons, T.base_outer]; exact hface))) }
  refine ⟨D, ?_⟩
  rw [← T.boundary]
  have hdeg : T.map.faceDegree T.outer = (T.base :: rest).length := by
    rw [← T.base_outer]
    exact hcyc.length_eq.symm
  show (T.base :: rest).map (fun d => T.vtx (T.map.vertexOf d)) ++
      [T.vtx (T.map.vertexOf ((T.base :: rest).head hcyc.ne_nil))] = _
  rw [hdeg]
  exact (ofFn_boundary_eq hcyc (fun d => T.vtx (T.map.vertexOf d))).symm

end CycleDisc

/-- **Splitting a boundary walk at a vertex.**  The vertex is the label of a dart of the
cycle, or it is the closing vertex. -/
theorem split_boundary {α β : Type*} (f : α → β) (z u : β) :
    ∀ (p q : List β) (l : List α), l.map f ++ [z] = p ++ u :: q →
      (∃ s b t, l = s ++ b :: t ∧ p = s.map f ∧ u = f b ∧ q = t.map f ++ [z]) ∨
        (p = l.map f ∧ u = z ∧ q = [])
  | [], q, [], h => by
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at h
      exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | [], q, b :: t, h => by
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      exact Or.inl ⟨[], b, t, rfl, rfl, h.1.symm, h.2.symm⟩
  | a :: p', q, [], h => by
      simp only [List.map_nil, List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.2.symm (by simp)
  | a :: p', q, c :: l', h => by
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      rcases split_boundary f z u p' q l' h.2 with ⟨s, b, t, hl, hp, hu, hq⟩ | ⟨hp, hu, hq⟩
      · exact Or.inl ⟨c :: s, b, t, by rw [hl]; rfl, by rw [hp, ← h.1]; rfl, hu, hq⟩
      · exact Or.inr ⟨by rw [hp, ← h.1]; rfl, hu, hq⟩

/-- **HC3(c): attaching a pendant edge at a boundary vertex.** -/
theorem attachPendantStatement : AttachPendantStatement X := by
  intro p q u v huv T
  obtain ⟨D, hD⟩ := CycleDisc.exists_of_triangulatedDisc T
  have h : D.cyc.map D.lab ++ [D.lab (D.cyc.head D.isFaceCycle.ne_nil)] = p ++ u :: q := hD
  rcases split_boundary D.lab _ u p q D.cyc h with ⟨s, b, t, hcyc, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨D', hD'⟩ := CycleDisc.attachPendant hcyc huv
    exact ⟨hD' ▸ D'.toTriangulatedDisc⟩
  · obtain ⟨D', hD'⟩ := CycleDisc.attachPendant_end huv
    exact ⟨hD' ▸ D'.toTriangulatedDisc⟩

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.ofFn_pow_eq_map_orbitWalk
#audit_axioms GroupApproximation.Systolic.isFaceCycle_pow_length
#audit_axioms GroupApproximation.Systolic.CycleDisc.toTriangulatedDisc
#audit_axioms GroupApproximation.Systolic.CycleDisc.exists_of_triangulatedDisc
#audit_axioms GroupApproximation.Systolic.split_boundary
#audit_axioms GroupApproximation.Systolic.attachPendantStatement
