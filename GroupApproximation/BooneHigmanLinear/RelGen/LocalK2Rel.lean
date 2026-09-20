import GroupApproximation.BooneHigmanLinear.RelGen.LocalDiag
import GroupApproximation.BooneHigmanLinear.RelGen.SteinCell3
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative `K₂` of a local ring lies in the symbols

Lane bh-pal-wire, k2-poly H.L1 (ii). `A` is local with maximal ideal `M`, and every pair of
indices avoids a third one.

**`rel_faith`**: an element of `qGroup M K = ⟨x_ij(M) : i, j ∈ K⟩ ⊔ H̄(A, M)` acting trivially on
`A^I` is a product of symbols. With `K = univ`, `St̄(A, M) ∩ K₂ ⊆ ⟨symbols⟩` (`relKer_act_le`).

The proof is Stein's induction (`SteinCell3`). At a new index `L ∉ K`, `g = c q r t` with
`c ∈ colG`, `q ∈ qGroup K`, `r ∈ rowG` and `t ∈ H̄`.
* `t` is diagonal and `q` scales `e_L` (`lscalGroup`), so `q r t e_L = μ e_L`. The column group
  `c` does not change the coordinate `L`, so `μ = 1` and `c e_L = e_L`, hence `c = 1`.
* `q` scales the row `L` and `t` scales `e_k`, so `(r e_k)_L = 0` for `k ≠ L`, hence `r = 1`.
* `q t ∈ qGroup K` acts trivially; induction. At `K = ∅`, `qGroup ∅ ⊆ T_univ`, and `torus_faith`
  applies.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec
  unitVec_apply act_mul act_eq_self_of_rootSpan act_apply_of_rootSpan eq_one_of_col_fix_finset
  eq_one_of_row_zero_finset)
open IsLocalRing

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] [IsLocalRing A]

theorem qGroup_empty_le : qGroup (maximalIdeal A) (∅ : Finset I) ≤ torusK I A Finset.univ := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr
    (Set.union_subset ?_ ?_))
  · rintro _ ⟨i, j, hij, s, ⟨hi, -⟩, -, rfl⟩
    exact absurd hi (Finset.notMem_empty i)
  · rintro _ ⟨i, j, hij, u, -, rfl⟩
    exact h_mem_torusK hij (Finset.mem_univ i) (Finset.mem_univ j) u
  · rintro _ ⟨i, j, hij, u, v, -, rfl⟩
    exact symGroup_le_torusK _ (csym_mem_symGroup hij u v)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_empty_le

/-- **Relative faithfulness up to symbols.** -/
theorem rel_faith (third : ThirdIndex I) (K : Finset I) :
    ∀ g ∈ qGroup (maximalIdeal A) K, (∀ y : I → A, act g y = y) → g ∈ symGroup I A := by
  induction K using Finset.induction_on with
  | empty => exact fun g hg hfix => torus_faith third Finset.univ g (qGroup_empty_le hg) hfix
  | insert L K hLK ih =>
    intro g hg hfix
    rw [qGroup_eq_closure] at hg
    have hB : g ∈ BSet A K L := by
      induction hg using Subgroup.closure_induction_left with
      | one => exact one_mem_BSet K L
      | mul_left x hx y _ hy => exact B_mul_gen third hLK hx hy
      | inv_mul_cancel x hx y _ hy => exact B_mul_gen third hLK (genSet_inv hx) hy
    obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hB
    obtain ⟨d, hd⟩ := hBar_le_diagGroup (maximalIdeal A) ht
    obtain ⟨⟨lq, hlq⟩, ⟨rq, hrq⟩⟩ := qGroup_le_lscal hLK hq
    have hL0 : ∀ j, j ∈ K → unitVec (R := A) L j = 0 := fun j hj => by
      rw [unitVec_apply, if_neg (fun e : j = L => hLK (by rw [← e]; exact hj))]
    have hrL : act r (unitVec L) = unitVec L :=
      act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hp => hL0 j hp.2)
        (rootGroup_le_rootSpan (fun _ _ hp => hp) hr)
    have hcL : ∀ v : I → A, act c v L = v L := fun v =>
      act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j = L) (k := L)
        (fun i _ hp hiL => hLK (by rw [← hiL]; exact hp.1))
        (rootGroup_le_rootSpan (fun _ _ hp => hp) hc) v
    -- Step 1: `c = 1`.
    have hqrt : act (q * r * t) (unitVec L) = ((d L * lq : Aˣ) : A) • unitVec L := by
      rw [act_mul, act_mul, diag_act_unitVec hd L, act_smul', hrL, act_smul', hlq, smul_smul,
        Units.val_mul]
    rw [show c * q * r * t = c * (q * r * t) by group] at hfix ⊢
    have hμ : ((d L * lq : Aˣ) : A) = 1 := by
      have e := congrFun (hfix (unitVec L)) L
      rw [act_mul, hqrt, hcL, Pi.smul_apply, smul_eq_mul, unitVec_apply, if_pos rfl,
        mul_one] at e
      exact e
    have hcfix : act c (unitVec L) = unitVec L := by
      have e := hfix (unitVec L)
      rwa [act_mul, hqrt, hμ, one_smul] at e
    obtain rfl : c = 1 := eq_one_of_col_fix_finset L K hLK c
      (rootGroup_le_rootSpan (fun _ _ hp => ⟨hp.2, hp.1⟩) hc) hcfix
    rw [one_mul] at hfix ⊢
    -- Step 2: `r = 1`.
    have hr1 : r = 1 := by
      refine eq_one_of_row_zero_finset L K hLK r (rootGroup_le_rootSpan (fun _ _ hp => hp) hr) ?_
      intro k hk
      have e := congrFun (hfix (unitVec k)) L
      rw [act_mul, act_mul, diag_act_unitVec hd k, act_smul', hrq, Pi.smul_apply, smul_eq_mul,
        unitVec_apply k L, if_neg (Ne.symm hk)] at e
      exact (Units.mul_right_eq_zero _).mp ((Units.mul_right_eq_zero _).mp e)
    subst hr1
    rw [mul_one] at hfix ⊢
    -- Step 3: induction.
    exact ih (q * t) (Subgroup.mul_mem _ hq (Subgroup.mem_sup_right ht)) hfix

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.rel_faith

/-- `St̄(A, M) ∩ K₂ ⊆ ⟨symbols⟩`. -/
theorem relKer_act_le (third : ThirdIndex I) {g : SteinbergGroup I A}
    (hg : g ∈ relKer I (maximalIdeal A)) (hfix : ∀ y : I → A, act g y = y) :
    g ∈ symGroup I A := by
  rw [relKer_eq_sup_hBar third] at hg
  refine rel_faith third Finset.univ g ((sup_le_sup_right ?_ _) hg) hfix
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, j, hij, s, hs, rfl⟩
  exact x_mem_rootGroup hij ⟨Finset.mem_univ i, Finset.mem_univ j⟩ hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.relKer_act_le

end GroupApproximation.BooneHigmanLinear.RelGen
