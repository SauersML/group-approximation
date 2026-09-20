import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleIndep
import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormCantor
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagonal prefix-cloning homomorphism

Clones in distinct first-letter cones commute in the presented all-swaps group,
using its conjugation relators rather than injectivity of boundary evaluation.
Their finite product therefore defines a group homomorphism. This is the
diagonal map used by the kernel product identity in `EnvelopeHigmanVCSwindleProd`.
It does not assert that this homomorphism fixes the evaluation kernel.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Generating swaps cloned into distinct first-letter cones commute. -/
theorem higSw_phi_letters_commute {d : ℕ} {a b : Fin d} (hab : a ≠ b)
    (x y u v : List (Fin d)) :
    Commute (higSw_phi d [a] (higmanVCCommon_mk d (FreeGroup.of (x, y))))
      (higSw_phi d [b] (higmanVCCommon_mk d (FreeGroup.of (u, v)))) := by
  simp only [higSw_phi_gen, List.singleton_append]
  by_cases hxy : ¬ a :: x <+: a :: y ∧ ¬ a :: y <+: a :: x
  · by_cases huv : ¬ b :: u <+: b :: v ∧ ¬ b :: v <+: b :: u
    · have hu := vgen_mapsCone_coneSwap_fix hxy.1 hxy.2
        (higSw_not_prefix_cons hab.symm u x) (higSw_not_prefix_cons hab x u)
        (higSw_not_prefix_cons hab.symm u y) (higSw_not_prefix_cons hab y u)
      have hv := vgen_mapsCone_coneSwap_fix hxy.1 hxy.2
        (higSw_not_prefix_cons hab.symm v x) (higSw_not_prefix_cons hab x v)
        (higSw_not_prefix_cons hab.symm v y) (higSw_not_prefix_cons hab y v)
      have hr := higmanVCCommon_mk_rel
        (higmanVCCommon_conj_mem hxy.1 hxy.2 hu hv huv.1 huv.2 huv.1 huv.2)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
      exact (commute_iff_eq _ _).mpr
        (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hr))
    · rw [higmanVCCommon_mk_comparable huv]
      exact Commute.one_right _
  · rw [higmanVCCommon_mk_comparable hxy]
    exact Commute.one_left _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_letters_commute

/-- All elements cloned into distinct first-letter cones commute. -/
theorem higSw_phi_commute {d : ℕ} {a b : Fin d} (hab : a ≠ b)
    (q r : higmanVCCommon_Q d) : Commute (higSw_phi d [a] q) (higSw_phi d [b] r) := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  obtain ⟨h, rfl⟩ := higmanVCTreeNF_mk_surjective d r
  have hletter : ∀ x y, Commute
      (higSw_phi d [a] (higmanVCCommon_mk d (FreeGroup.of (x, y))))
      (higSw_phi d [b] (higmanVCCommon_mk d h)) := by
    intro x y
    induction h using FreeGroup.induction_on with
    | C1 => simp only [map_one]; exact Commute.one_right _
    | of p => exact higSw_phi_letters_commute hab x y p.1 p.2
    | inv_of p ih => simpa only [map_inv] using ih.inv_right
    | mul h₁ h₂ ih₁ ih₂ => simpa only [map_mul] using ih₁.mul_right ih₂
  induction g using FreeGroup.induction_on with
  | C1 => simp only [map_one]; exact Commute.one_left _
  | of p => exact hletter p.1 p.2
  | inv_of p ih => simpa only [map_inv] using ih.inv_left
  | mul g₁ g₂ ih₁ ih₂ => simpa only [map_mul] using ih₁.mul_left ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_commute

/-- The product of a duplicate-free list of first-letter clones preserves multiplication. -/
theorem higSw_diag_list_mul {d : ℕ} (l : List (Fin d)) (hl : l.Nodup)
    (q r : higmanVCCommon_Q d) :
    (l.map (fun a => higSw_phi d [a] (q * r))).prod =
      (l.map (fun a => higSw_phi d [a] q)).prod *
        (l.map (fun a => higSw_phi d [a] r)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnodup := List.nodup_cons.mp hl
    have hc : Commute (higSw_phi d [a] r)
        (l.map (fun b => higSw_phi d [b] q)).prod := by
      refine Commute.list_prod_right _ _ ?_
      intro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact higSw_phi_commute (a := a) (b := b)
        (fun e => hnodup.1 (by simpa only [e] using hb)) r q
    simp only [List.map_cons, List.prod_cons]
    rw [ih hnodup.2, map_mul]
    calc
      (higSw_phi d [a] q * higSw_phi d [a] r) *
          ((l.map (fun b => higSw_phi d [b] q)).prod *
            (l.map (fun b => higSw_phi d [b] r)).prod) =
          higSw_phi d [a] q *
            ((higSw_phi d [a] r * (l.map (fun b => higSw_phi d [b] q)).prod) *
              (l.map (fun b => higSw_phi d [b] r)).prod) := by group
      _ = _ := by rw [hc.eq]; simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag_list_mul

/-- Simultaneously clone an element into every first-letter cone. -/
noncomputable def higSw_diag (d : ℕ) : higmanVCCommon_Q d →* higmanVCCommon_Q d where
  toFun q := ((List.finRange d).map fun a => higSw_phi d [a] q).prod
  map_one' := by simp
  map_mul' q r := higSw_diag_list_mul _ (List.nodup_finRange d) q r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag

/-- Boundary evaluation of the diagonal is the first-level product of localizations. -/
theorem higSw_E_diag {d : ℕ} (q : higmanVCCommon_Q d) :
    ((higmanVCTreeNF_E d (higSw_diag d q) : ↥(higmanThompsonV (Fin d))) :
        Equiv.Perm (Cantor (Fin d))) =
      nfLevelProd (List.finRange d) (fun _ =>
        ((higmanVCTreeNF_E d q : ↥(higmanThompsonV (Fin d))) :
          Equiv.Perm (Cantor (Fin d)))) := by
  change ((higmanThompsonV (Fin d)).subtype.comp (higmanVCTreeNF_E d))
    (((List.finRange d).map fun a => higSw_phi d [a] q).prod) = _
  rw [map_list_prod]
  simp only [List.map_map, nfLevelProd]
  apply congrArg List.prod
  exact List.map_congr_left fun a _ => higSw_E_phi [a] q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_E_diag

/-- The diagonal carries each prefixed cone by the same suffix-preserving table. -/
theorem higSw_diag_mapsCone {d : ℕ} (q : higmanVCCommon_Q d)
    {x y : List (Fin d)}
    (h : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) x y)
    (a : Fin d) :
    MapsCone (higmanVCTreeNF_E d (higSw_diag d q) : Equiv.Perm (Cantor (Fin d)))
      ([a] ++ x) ([a] ++ y) := by
  intro z
  rw [higSw_E_diag, prepend_append,
    nfLevelProd_apply_of_mem _ a _ _ (List.nodup_finRange d) (List.mem_finRange a),
    h z, prepend_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag_mapsCone

/-- The diagonal preserves the evaluation kernel, without asserting that it fixes it. -/
theorem higSw_diag_ker {d : ℕ} {q : higmanVCCommon_Q d}
    (hq : q ∈ (higmanVCTreeNF_E d).ker) :
    higSw_diag d q ∈ (higmanVCTreeNF_E d).ker := by
  change ((List.finRange d).map fun a => higSw_phi d [a] q).prod ∈ _
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  exact higSw_phi_ker [a] hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag_ker

end GroupApproximation.BooneHigman.Metabelian.Envelope
