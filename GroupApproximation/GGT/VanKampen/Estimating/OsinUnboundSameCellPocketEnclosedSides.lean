import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# The far side of a same-face edge along its face

Osin (math/0411039v3, §9), proof of Lemma 9.4.  Let `d` be a dart of a planar map whose reverse lies
on the same face, with the face traversal `d, f d, …, f^{n-1} d` and `f^{m+1} d = α d`.  Moves that
avoid the edge of `d` split the darts into the side of `d` and the side of `α d`
(`AvoidEdgeStep.not_eqvGen_alpha_of_sameFace`).  This module records the side of `α d`, the far side,
along the face.

* `Far`, `farFaces`: the far darts, and the faces other than the face of `d` with a far dart.
* `far_iff_mem_farFaces`: every dart of a face other than the face of `d` is far exactly when the face
  is a far face.
* `far_alpha_iff`: a reversal at another edge keeps the side.
* `far_pow`, `not_far_pow`: along the face, `f^t d` is far exactly for `1 ≤ t ≤ m + 1`.
* `pocketWalk`, `mem_pocketWalk`: the face walk `f d, …, fᵐ d` strictly between `d` and `α d`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

namespace SameCellPocketEnclosed

variable {M : CombMap.{v}}

/-- A dart is **far** from `d` when moves that avoid the edge of `d` join it to `α d`. -/
abbrev Far (M : CombMap.{v}) (d x : M.Dart) : Prop :=
  Relation.EqvGen (AvoidEdgeStep M d) x (M.alpha d)

open scoped Classical in
/-- The faces other than the face of `d` that hold a far dart. -/
noncomputable def farFaces (M : CombMap.{v}) (d : M.Dart) : Finset M.Face :=
  Finset.univ.filter fun F => F ≠ M.faceOf d ∧ ∃ x, M.faceOf x = F ∧ Far M d x

theorem mem_farFaces {d : M.Dart} {F : M.Face} :
    F ∈ farFaces M d ↔ F ≠ M.faceOf d ∧ ∃ x, M.faceOf x = F ∧ Far M d x := by
  classical
  simp only [farFaces, Finset.mem_filter, Finset.mem_univ, true_and]

theorem faceOf_not_mem_farFaces (d : M.Dart) : M.faceOf d ∉ farFaces M d :=
  fun h => (mem_farFaces.mp h).1 rfl

/-- **A face other than the face of `d` lies on one side.** -/
theorem far_iff_mem_farFaces {d x : M.Dart} (hface : M.faceOf (M.alpha d) = M.faceOf d)
    (hx : M.faceOf x ≠ M.faceOf d) : Far M d x ↔ M.faceOf x ∈ farFaces M d := by
  rw [mem_farFaces]
  constructor
  · intro h
    exact ⟨hx, x, rfl, h⟩
  · rintro ⟨-, y, hy, hfar⟩
    have hxy : Relation.EqvGen (AvoidEdgeStep M d) x y :=
      AvoidEdgeStep.eqvGen_of_faceOf_eq (d := d) hy.symm (fun h => hx h.symm)
        (fun h => hx (h.symm.trans hface))
    exact .trans _ _ _ hxy hfar

/-- **A reversal at another edge keeps the side.** -/
theorem far_alpha_iff {d x : M.Dart} (hxd : x ≠ d) (hxa : x ≠ M.alpha d) :
    Far M d (M.alpha x) ↔ Far M d x := by
  have hstep : Relation.EqvGen (AvoidEdgeStep M d) x (M.alpha x) :=
    .rel _ _ (Or.inr ⟨hxd, hxa, rfl⟩)
  exact ⟨fun h => .trans _ _ _ hstep h, fun h => .trans _ _ _ (.symm _ _ hstep) h⟩

theorem facePerm_eq_sigma_alpha (x : M.Dart) : M.facePerm x = M.sigma (M.alpha x) := rfl

section Along

variable {d : M.Dart} {n m : ℕ}

/-- **Along the face, `f^t d` is far for `1 ≤ t ≤ m + 1`.** -/
theorem far_pow (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) d = (M.facePerm ^ b) d → a = b)
    (hmn : m + 1 < n) (hm : (M.facePerm ^ (m + 1)) d = M.alpha d) {t : ℕ} (h1 : 1 ≤ t)
    (ht : t ≤ m + 1) : Far M d ((M.facePerm ^ t) d) := by
  have hstart : Far M d ((M.facePerm ^ 1) d) := by
    rw [pow_one, facePerm_eq_sigma_alpha]
    exact .symm _ _ (.rel _ _ (Or.inl rfl))
  have hrun := AvoidEdgeStep.eqvGen_facePerm_pow_of_le (d := d) d h1 fun s hs hst => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hinj s 0 (by omega) (by omega) (by rw [pow_zero, Equiv.Perm.one_apply]; exact h)
      omega
    · have := hinj s (m + 1) (by omega) hmn (h.trans hm.symm)
      omega
  exact .trans _ _ _ (.symm _ _ hrun) hstart

/-- **Along the face, `f^t d` is joined to `d` for `m + 2 ≤ t ≤ n`.** -/
theorem near_pow (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) d = (M.facePerm ^ b) d → a = b)
    (hmn : m + 1 < n) (hm : (M.facePerm ^ (m + 1)) d = M.alpha d)
    {t : ℕ} (h1 : m + 2 ≤ t) (ht : t ≤ n) :
    Relation.EqvGen (AvoidEdgeStep M d) ((M.facePerm ^ t) d) d := by
  have havoid : ∀ s, m + 2 ≤ s → s < n →
      (M.facePerm ^ s) d ≠ d ∧ (M.facePerm ^ s) d ≠ M.alpha d := by
    intro s hs hsn
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hinj s 0 hsn (by omega) (by rw [pow_zero, Equiv.Perm.one_apply]; exact h)
      omega
    · have := hinj s (m + 1) hsn hmn (h.trans hm.symm)
      omega
  have hsig : (M.facePerm ^ (m + 2)) d = M.sigma d := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ', Equiv.Perm.mul_apply, hm,
      facePerm_eq_sigma_alpha, M.alpha_involutive]
  have hstart : Relation.EqvGen (AvoidEdgeStep M d) ((M.facePerm ^ (m + 2)) d) d := by
    rw [hsig]
    exact .symm _ _ (.rel _ _ (Or.inl rfl))
  have hrun := AvoidEdgeStep.eqvGen_facePerm_pow_of_le (d := d) d h1
    fun s hs hst => havoid s hs (lt_of_lt_of_le hst ht)
  exact .trans _ _ _ (.symm _ _ hrun) hstart

/-- **Along the face, `f^t d` is not far for `t = 0` or `m + 2 ≤ t < n`.** -/
theorem not_far_pow (hM : M.IsPlanar) (hface : M.faceOf (M.alpha d) = M.faceOf d)
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) d = (M.facePerm ^ b) d → a = b)
    (hmn : m + 1 < n) (hm : (M.facePerm ^ (m + 1)) d = M.alpha d)
    {t : ℕ} (ht : t = 0 ∨ (m + 2 ≤ t ∧ t < n)) : ¬ Far M d ((M.facePerm ^ t) d) := by
  intro hfar
  have hnear : Relation.EqvGen (AvoidEdgeStep M d) ((M.facePerm ^ t) d) d := by
    rcases ht with rfl | ⟨h1, h2⟩
    · rw [pow_zero, Equiv.Perm.one_apply]
      exact .refl _
    · exact near_pow hinj hmn hm h1 h2.le
  exact AvoidEdgeStep.not_eqvGen_alpha_of_sameFace M hM d hface.symm
    (.trans _ _ _ (.symm _ _ hnear) hfar)

/-- **The far darts of the face of `d` other than `α d` are `f d, …, fᵐ d`.** -/
theorem far_pow_iff (hM : M.IsPlanar) (hface : M.faceOf (M.alpha d) = M.faceOf d)
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) d = (M.facePerm ^ b) d → a = b)
    (hmn : m + 1 < n) (hm : (M.facePerm ^ (m + 1)) d = M.alpha d)
    {t : ℕ} (htn : t < n) : Far M d ((M.facePerm ^ t) d) ↔ 1 ≤ t ∧ t ≤ m + 1 := by
  constructor
  · intro hfar
    by_contra hnot
    refine not_far_pow hM hface hinj hmn hm ?_ hfar
    rcases Nat.eq_zero_or_pos t with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, htn⟩
  · rintro ⟨h1, h2⟩
    exact far_pow hinj hmn hm h1 h2

end Along

/-- The face walk strictly between `d` and `α d`: `f d, …, fᵐ d`. -/
def pocketWalk (M : CombMap.{v}) (d : M.Dart) (m : ℕ) : List M.Dart :=
  (List.range m).map fun t => (M.facePerm ^ (t + 1)) d

theorem mem_pocketWalk {d x : M.Dart} {m : ℕ} :
    x ∈ pocketWalk M d m ↔ ∃ t < m, (M.facePerm ^ (t + 1)) d = x := by
  simp only [pocketWalk, List.mem_map, List.mem_range]

theorem pocketWalk_length (d : M.Dart) (m : ℕ) : (pocketWalk M d m).length = m := by
  simp only [pocketWalk, List.length_map, List.length_range]

theorem pocketWalk_getElem (d : M.Dart) (m : ℕ) {k : ℕ} (hk : k < (pocketWalk M d m).length) :
    (pocketWalk M d m)[k] = (M.facePerm ^ (k + 1)) d := by
  simp only [pocketWalk, List.getElem_map, List.getElem_range]

end SameCellPocketEnclosed

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.SameCellPocketEnclosed

#audit_axioms mem_farFaces
#audit_axioms far_iff_mem_farFaces
#audit_axioms far_alpha_iff
#audit_axioms far_pow
#audit_axioms near_pow
#audit_axioms not_far_pow
#audit_axioms far_pow_iff
#audit_axioms mem_pocketWalk
#audit_axioms pocketWalk_getElem
