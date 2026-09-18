import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllFamEq
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The symmetric path antichain and the `N`-conjugation closure (lane bh-met-92d)

Notation as in `EnvelopeHigmanVCOrbitAllPath`: `t = m(a, b)` with `a`, `b` incomparable,
`U = higmanVCTreeNF_U d`, `S = higmanVCTreeNFWitPivot_S d`.

* `higmanVCOrbitLong_D a b P = a · pathSet P ∪ b · pathSet P` is an antichain
  (`higmanVCOrbitLong_D_isAC`), and it contains the pivot in its subgroup
  (`higmanVCOrbitLong_t_mem`): peel the path `P` off `t` (`higmanVCOrbitAll_path_mem`) and
  split `m(a P, b P)` over the children `P i`.
* `higmanVCOrbitLong_path_mem_S`: for `f, g ∈ pathSet P`, `m(a f, b g) · t ∈ H_D ⊆ S`.
* `higmanVCOrbitLong_conj_mem_S` (**`N`-conjugation**): if `h t ∈ S`, `x ∈ U` and
  `t x t⁻¹ ∈ U`, then `(x h x⁻¹) t = x (h t) (t x t⁻¹)⁻¹ ∈ S`.  This uses only `t² = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The symmetric path antichain `a · pathSet P ∪ b · pathSet P`. -/
def higmanVCOrbitLong_D {d : ℕ} (a b P : List (Fin d)) : Finset (List (Fin d)) :=
  (higmanVCOrbitAll_pathSet P).image (a ++ ·) ∪ (higmanVCOrbitAll_pathSet P).image (b ++ ·)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_D

theorem higmanVCOrbitLong_mem_D_a {d : ℕ} {a b P e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitAll_pathSet P) (hu : a ++ e = u) :
    u ∈ higmanVCOrbitLong_D a b P := by
  rw [higmanVCOrbitLong_D]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_mem_D_a

theorem higmanVCOrbitLong_mem_D_b {d : ℕ} {a b P e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitAll_pathSet P) (hu : b ++ e = u) :
    u ∈ higmanVCOrbitLong_D a b P := by
  rw [higmanVCOrbitLong_D]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_mem_D_b

/-- The symmetric path antichain is an antichain. -/
theorem higmanVCOrbitLong_D_isAC {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (P : List (Fin d)) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCOrbitLong_D a b P) := by
  have hA := higmanVCOrbitAll_pathSet_isAC P
  intro u hu v hv huv hpre
  simp only [higmanVCOrbitLong_D, Finset.mem_union, Finset.mem_image] at hu hv
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hv with ⟨e', he', rfl⟩ | ⟨e', -, rfl⟩
    · exact hA e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj a).mp hpre)
    · exact higmanVCOrbitGap_incomp_append hab hba e e' hpre
  · rcases hv with ⟨e', -, rfl⟩ | ⟨e', he', rfl⟩
    · exact higmanVCOrbitGap_incomp_append hba hab e e' hpre
    · exact hA e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj b).mp hpre)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_D_isAC

/-- The pivot lies in the subgroup of the symmetric path antichain. -/
theorem higmanVCOrbitLong_t_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (P : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitLong_D a b P) := by
  have hK : ∀ (q : List (Fin d)) (y j : Fin d), q ++ [y] <+: P → j ≠ y →
      higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [j], b ++ q ++ [j])) ∈
        higmanVCTreeNFWitPivot_H d (higmanVCOrbitLong_D a b P) := fun q y j hq hj =>
    higmanVCLeafExp_letter_mem_H
      (higmanVCOrbitLong_mem_D_a (higmanVCOrbitAll_mem_sib P q y j hq hj) (by simp))
      (higmanVCOrbitLong_mem_D_b (higmanVCOrbitAll_mem_sib P q y j hq hj) (by simp))
  have hpath := higmanVCOrbitAll_path_mem P a b hab hba hK
  have pa : a <+: a ++ P := List.prefix_append a P
  have pb : b <+: b ++ P := List.prefix_append b P
  have hP : higmanVCCommon_mk d (FreeGroup.of (a ++ P, b ++ P)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitLong_D a b P) := by
    rw [higmanVCCommon_mk_split (higmanVCOrbitGen_incomp hab hba pa pb)
      (higmanVCOrbitGen_incomp hba hab pb pa), higmanVC_splitAll]
    exact higmanVCOrbitGen_split_mem (a ++ P) (b ++ P) (List.finRange d) fun i _ =>
      higmanVCLeafExp_letter_mem_H
        (higmanVCOrbitLong_mem_D_a (higmanVCOrbitAll_mem_child P i) (by simp))
        (higmanVCOrbitLong_mem_D_b (higmanVCOrbitAll_mem_child P i) (by simp))
  have e := Subgroup.mul_mem _ hP hpath
  rwa [mul_inv_cancel_left] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_t_mem

/-- **Path discharge.**  For `f, g ∈ pathSet P`, `m(a f, b g) · t ∈ H_D ⊆ S`. -/
theorem higmanVCOrbitLong_path_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {P f g : List (Fin d)} (hf : f ∈ higmanVCOrbitAll_pathSet P)
    (hg : g ∈ higmanVCOrbitAll_pathSet P) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ f, b ++ g)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have hm : higmanVCCommon_mk d (FreeGroup.of (a ++ f, b ++ g)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
        higmanVCTreeNFWitPivot_H d (higmanVCOrbitLong_D a b P) :=
    Subgroup.mul_mem _ (higmanVCLeafExp_letter_mem_H (higmanVCOrbitLong_mem_D_a hf rfl)
      (higmanVCOrbitLong_mem_D_b hg rfl)) (higmanVCOrbitLong_t_mem hab hba P)
  exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, Subgroup.one_mem _, higmanVCOrbitLong_D a b P,
    higmanVCOrbitLong_D_isAC hab hba P, _, hm, 1, Subgroup.one_mem _,
    by simp only [one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_path_mem_S

/-- **`N`-conjugation.**  If `h t ∈ S`, `x ∈ U` and `t x t⁻¹ ∈ U`, then `(x h x⁻¹) t ∈ S`. -/
theorem higmanVCOrbitLong_conj_mem_S {d : ℕ} {a b : List (Fin d)} {h x : higmanVCCommon_Q d}
    (hh : h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d)
    (hx : x ∈ higmanVCTreeNF_U d)
    (htx : higmanVCCommon_mk d (FreeGroup.of (a, b)) * x *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ ∈ higmanVCTreeNF_U d) :
    x * h * x⁻¹ * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have hsq : higmanVCCommon_mk d (FreeGroup.of (a, b)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) = 1 := higmanVCCommon_mk_sq a b
  have ht2 : (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a, b)) := inv_eq_of_mul_eq_one_right hsq
  have e : x * h * x⁻¹ * higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      x * (h * higmanVCCommon_mk d (FreeGroup.of (a, b))) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)) * x *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)⁻¹ := by
    calc x * h * x⁻¹ * higmanVCCommon_mk d (FreeGroup.of (a, b))
        = x * h * (higmanVCCommon_mk d (FreeGroup.of (a, b)) *
            higmanVCCommon_mk d (FreeGroup.of (a, b))) * x⁻¹ *
              (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ := by rw [hsq, mul_one, ht2]
      _ = x * (h * higmanVCCommon_mk d (FreeGroup.of (a, b))) *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)) * x *
            (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)⁻¹ := by group
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U (higmanVCPivotAC_U_mul_S hx hh) (Subgroup.inv_mem _ htx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_conj_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
