import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.ConfigStep
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.SOLVABLE_MODULE
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Equivalent configurations give equal configuration elements

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`: the "only if"
direction of Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Theorem `tmm`(b), with
equation `(e000)`.

The normal closure `T` of the letters `x_u` in `G(M)` is abelian, because any two
conjugates of `x`-letters commute (`KMS.conj_x_commute`).  `T` contains every
`x_{q_j A_0}`, so one machine step preserves `configElem M` (`configElem_eq_of_step`).
Induction on the equivalence closure then gives `configElem_eq_of_equiv`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

variable {K N : ℕ}

namespace Forward

/-- The letters `x_u`, `u = q_j ∏_{i ∈ S} A_i`, in `G(M)`. -/
def xLetters (M : Minsky.Machine K N) : Set (KhGroup M) :=
  Set.range (fun p : Fin (N + 1) × Finset (Fin (K + 1)) ↦
    (PresentedGroup.of (KhGen.x p.1 p.2) : KhGroup M))

/-- The normal closure of the `x`-letters in `G(M)`. -/
def xSub (M : Minsky.Machine K N) : Subgroup (KhGroup M) :=
  Subgroup.normalClosure (xLetters M)

instance xSub_normal (M : Minsky.Machine K N) : (xSub M).Normal :=
  Subgroup.normalClosure_normal

theorem conjugates_x_commute (M : Minsky.Machine K N) :
    ∀ a ∈ Group.conjugatesOfSet (xLetters M), ∀ b ∈ Group.conjugatesOfSet (xLetters M),
      Commute a b := by
  intro a ha b hb
  obtain ⟨x, hx, hxa⟩ := Group.mem_conjugatesOfSet_iff.mp ha
  obtain ⟨y, hy, hyb⟩ := Group.mem_conjugatesOfSet_iff.mp hb
  obtain ⟨p, rfl⟩ := Set.mem_range.mp hx
  obtain ⟨q, rfl⟩ := Set.mem_range.mp hy
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxa
  obtain ⟨g', rfl⟩ := isConj_iff.mp hyb
  have hc := conj_x_commute M p.1 q.1 p.2 q.2 g⁻¹ g'⁻¹
  rw [inv_inv, inv_inv] at hc
  exact hc

/-- The normal closure of the `x`-letters is abelian. -/
theorem xSub_commute (M : Minsky.Machine K N) :
    ∀ u ∈ xSub M, ∀ v ∈ xSub M, Commute u v := by
  have h1 : Subgroup.closure (Group.conjugatesOfSet (xLetters M)) ≤
      Subgroup.centralizer (Group.conjugatesOfSet (xLetters M)) :=
    (Subgroup.closure_le (Subgroup.centralizer (Group.conjugatesOfSet (xLetters M)))).mpr
      fun a ha ↦ (Subgroup.mem_centralizer_iff (g := a)
        (s := Group.conjugatesOfSet (xLetters M))).mpr
          fun b hb ↦ (conjugates_x_commute M b hb a ha).eq
  have h2 : Subgroup.closure (Group.conjugatesOfSet (xLetters M)) ≤
      Subgroup.centralizer
        (Subgroup.closure (Group.conjugatesOfSet (xLetters M)) : Set (KhGroup M)) :=
    (Subgroup.closure_le (Subgroup.centralizer
      (Subgroup.closure (Group.conjugatesOfSet (xLetters M)) : Set (KhGroup M)))).mpr
      fun a ha ↦ (Subgroup.mem_centralizer_iff (g := a)
        (s := (Subgroup.closure (Group.conjugatesOfSet (xLetters M)) : Set (KhGroup M)))).mpr
          fun b hb ↦ ((Subgroup.mem_centralizer_iff (g := b)
            (s := Group.conjugatesOfSet (xLetters M))).mp (h1 hb) a ha).symm
  intro u hu v hv
  exact (Subgroup.mem_centralizer_iff (g := v)
    (s := (Subgroup.closure (Group.conjugatesOfSet (xLetters M)) : Set (KhGroup M)))).mp
      (h2 hv) u hu

theorem kLet_x_mem (M : Minsky.Machine K N) (j : Fin (N + 1)) :
    kLet M (.x j {0}) ∈ (xSub M : Set (KhGroup M)) := by
  have hmem : kLet M (.x j {0}) ∈ xLetters M := Set.mem_range.mpr ⟨(j, {0}), rfl⟩
  exact Subgroup.subset_normalClosure hmem

end Forward

/-- KMS `(e000)`: one step of the machine preserves the configuration element. -/
theorem configElem_eq_of_step (M : Minsky.Machine K N) {c d : Minsky.Cfg K N}
    (h : M.Step c d) : configElem M c = configElem M d :=
  Forward.configElem_eq_of_step_of_abelian M (T := Forward.xSub M) (Forward.xSub_commute M)
    (Forward.kLet_x_mem M) h

/-- KMS Theorem `tmm`(b), "only if": equivalent configurations have equal configuration
elements in `G(M)`. -/
theorem configElem_eq_of_equiv (M : Minsky.Machine K N) {c d : Minsky.Cfg K N}
    (h : M.Equiv c d) : configElem M c = configElem M d := by
  have key : ∀ c d : Minsky.Cfg K N, Relation.EqvGen M.Step c d →
      configElem M c = configElem M d := by
    intro c d hcd
    induction hcd with
    | rel _ _ hxy => exact configElem_eq_of_step M hxy
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact key c d h

end KMS

end GroupApproximation.Full.Kharlampovich
