import GroupApproximation.GGT.VanKampen.PermFirstReturnComposition
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity

/-!
# Constructing the actual boundary permutation of a face set

On selected face darts, cross an internal edge and otherwise stay on the
boundary side; then advance around the resulting face. First return of this
permutation to boundary darts constructs the boundary successor. Its
intermediate steps cross only internal edges, so it supplies the genuine
boundary walk rather than an arbitrary ordering of the same finite set.

This construction needs neither a supplied boundary list nor planarity.
Its orbits will enumerate the separate boundary components.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

open Equiv
universe v

namespace FaceSetCircuits

variable (M : CombMap.{v}) (faces : Finset M.Face)

abbrev SelectedDart := {d : M.Dart // M.faceOf d ∈ faces}

noncomputable instance selectedDartFintype : Fintype (SelectedDart M faces) :=
  Fintype.ofFinite _

noncomputable instance boundaryDartFintype : Fintype (BoundaryDart M faces) :=
  Fintype.ofFinite _

/-- Internal edges are crossed; boundary darts are fixed. -/
noncomputable def cross (d : SelectedDart M faces) : SelectedDart M faces := by
  classical
  exact if h : M.faceOf (M.alpha d.1) ∈ faces then ⟨M.alpha d.1, h⟩ else d

theorem cross_of_mem (d : SelectedDart M faces) (h : M.faceOf (M.alpha d.1) ∈ faces) :
    cross M faces d = ⟨M.alpha d.1, h⟩ := dif_pos h

theorem cross_of_notMem (d : SelectedDart M faces) (h : M.faceOf (M.alpha d.1) ∉ faces) :
    cross M faces d = d := dif_neg h

theorem cross_involutive : Function.Involutive (cross M faces) := by
  classical
  intro d
  by_cases h : M.faceOf (M.alpha d.1) ∈ faces
  · have hret : M.faceOf (M.alpha (M.alpha d.1)) ∈ faces := by
      rw [M.alpha_involutive]; exact d.2
    rw [cross_of_mem M faces d h, cross_of_mem M faces _ hret]
    exact Subtype.ext (M.alpha_involutive d.1)
  · rw [cross_of_notMem M faces d h, cross_of_notMem M faces d h]

noncomputable def crossPerm : Perm (SelectedDart M faces) where
  toFun := cross M faces
  invFun := cross M faces
  left_inv := cross_involutive M faces
  right_inv := cross_involutive M faces

/-- Rotation retains the selected face of a dart. -/
def selectedFacePerm : Perm (SelectedDart M faces) where
  toFun d := ⟨M.facePerm d.1, by rw [M.faceOf_facePerm]; exact d.2⟩
  invFun d := ⟨M.facePerm.symm d.1, by
    have h := M.faceOf_facePerm (M.facePerm.symm d.1)
    rw [M.facePerm.apply_symm_apply] at h
    rw [← h]; exact d.2⟩
  left_inv d := Subtype.ext (M.facePerm.symm_apply_apply d.1)
  right_inv d := Subtype.ext (M.facePerm.apply_symm_apply d.1)

noncomputable def step : Perm (SelectedDart M faces) :=
  selectedFacePerm M faces * crossPerm M faces

def boundaryEmbedding : BoundaryDart M faces ↪ SelectedDart M faces where
  toFun d := ⟨d.1, d.2.1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun d : SelectedDart M faces => d.1) h)

theorem mem_boundaryEmbedding_range (d : SelectedDart M faces) :
    d ∈ Set.range (boundaryEmbedding M faces) ↔ IsBoundaryDart M faces d.1 := by
  constructor
  · rintro ⟨b, rfl⟩; exact b.2
  · intro h; exact ⟨⟨d.1, h⟩, rfl⟩

theorem internal_of_not_boundary (d : SelectedDart M faces)
    (h : d ∉ Set.range (boundaryEmbedding M faces)) : InternalDart M faces d.1 := by
  classical
  refine ⟨d.2, ?_⟩
  by_contra ha
  exact h ((mem_boundaryEmbedding_range M faces d).mpr ⟨d.2, ha⟩)

theorem step_boundary_val (d : BoundaryDart M faces) :
    (step M faces (boundaryEmbedding M faces d)).1 = M.facePerm d.1 := by
  change M.facePerm (cross M faces ⟨d.1, d.2.1⟩).1 = M.facePerm d.1
  rw [cross_of_notMem M faces _ d.2.2]

theorem step_internal_val (d : SelectedDart M faces)
    (h : InternalDart M faces d.1) : (step M faces d).1 = M.sigma d.1 := by
  change M.facePerm (cross M faces d).1 = M.sigma d.1
  rw [cross_of_mem M faces d h.2]
  change M.sigma (M.alpha (M.alpha d.1)) = M.sigma d.1
  rw [M.alpha_involutive]

/-- Iterates avoiding the boundary are actual internal-edge walk steps. -/
theorem skip_walk (d : SelectedDart M faces) (n : ℕ)
    (hskip : ∀ k, k < n →
      (step M faces ^ k) d ∉ Set.range (boundaryEmbedding M faces)) :
    Relation.ReflTransGen (fun x y => InternalDart M faces x ∧ M.sigma x = y)
      d.1 ((step M faces ^ n) d).1 := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      have h := internal_of_not_boundary M faces _ (hskip n (by omega))
      have hp := ih (fun k hk => hskip k (by omega))
      apply hp.tail
      refine ⟨h, ?_⟩
      rw [pow_succ', Perm.mul_apply]
      exact (step_internal_val M faces _ h).symm

/-- The actual first return to the oriented boundary. -/
noncomputable def boundaryPerm : Perm (BoundaryDart M faces) :=
  Classical.choose (PermFirstReturn.exists_firstReturn
    (step M faces) (boundaryEmbedding M faces))

theorem boundaryPerm_firstReturn : PermFirstReturn.IsFirstReturn
    (step M faces) (boundaryPerm M faces) (boundaryEmbedding M faces) :=
  Classical.choose_spec (PermFirstReturn.exists_firstReturn
    (step M faces) (boundaryEmbedding M faces))

/-- Every constructed successor follows the original face-set boundary. -/
theorem boundaryPerm_walk (d : BoundaryDart M faces) :
    BoundaryWalk M faces d.1 (boundaryPerm M faces d).1 := by
  obtain ⟨m, hm, heq, hskip⟩ := boundaryPerm_firstReturn M faces d
  let p := step M faces
  let e := boundaryEmbedding M faces
  have hpath := skip_walk M faces (p (e d)) (m - 1) (by
    intro k hk
    have h : (p ^ (k + 1)) (e d) ∉ Set.range e := hskip (k + 1) (by omega) (by omega)
    simpa only [pow_succ, Perm.mul_apply] using h)
  have hend : (p ^ (m - 1)) (p (e d)) = e (boundaryPerm M faces d) := by
    rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hm]
    exact heq
  rw [hend] at hpath
  change BoundaryWalk M faces d.1 (boundaryPerm M faces d).1
  unfold BoundaryWalk
  rw [← step_boundary_val M faces d]
  exact hpath

end FaceSetCircuits
end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_walk
