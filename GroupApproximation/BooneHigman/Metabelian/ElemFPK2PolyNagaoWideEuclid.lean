import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideStab
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 3: multi-coordinate Euclidean reduction

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyNagaoWideStab`; `J = K \ {m}`.

* `k2PolyNagaoWide_nu f = natDegree f + 1` (`0` at `f = 0`), and
  `k2PolyNagaoWide_mu K m v = 2 ∑_{j ∈ J} ν(v j) + ν(v m)`.
* `k2PolyNagaoWide_step`: if some `v j ≠ 0` (`j ∈ J`), one root element of `S_K` lowers `μ`:
  `x_jm(-1) x_mj(1)` when `v m = 0`; `x_jm(-(v j / v m))` when `ν(v m) ≤ ν(v j)`;
  `x_mj(-(v m / v j))` otherwise.
* `k2PolyNagaoWide_clear`: some `s ∈ S_K` clears every `J`-coordinate (strong induction on `μ`).
* `k2PolyNagaoWide_rep_exists`: every `v` in the orbit `G e_L` is `q r` with `q ∈ S_K ≤ Q` and
  `r` supported on `{m, L}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one act_x_apply unitVec unitVec_apply x_mem_rootSpan act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

open Classical in
/-- `ν f = natDegree f + 1` for `f ≠ 0`, and `ν 0 = 0`. -/
noncomputable def k2PolyNagaoWide_nu (f : Polynomial (ZMod p)) : ℕ :=
  if f = 0 then 0 else f.natDegree + 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu

/-- `μ v = 2 ∑_{j ∈ K \ {m}} ν(v j) + ν(v m)`. -/
noncomputable def k2PolyNagaoWide_mu (K : Finset I) (m : I) (v : I → Polynomial (ZMod p)) : ℕ :=
  2 * ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (v i) + k2PolyNagaoWide_nu (v m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_mu

omit [Fact p.Prime] in
theorem k2PolyNagaoWide_nu_zero : k2PolyNagaoWide_nu (0 : Polynomial (ZMod p)) = 0 := by
  unfold k2PolyNagaoWide_nu
  rw [if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_zero

omit [Fact p.Prime] in
theorem k2PolyNagaoWide_nu_pos {f : Polynomial (ZMod p)} (hf : f ≠ 0) :
    0 < k2PolyNagaoWide_nu f := by
  unfold k2PolyNagaoWide_nu
  rw [if_neg hf]
  exact Nat.succ_pos _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_pos

/-- `ν(f % g) < ν g` for `g ≠ 0`. -/
theorem k2PolyNagaoWide_nu_mod_lt (f : Polynomial (ZMod p)) {g : Polynomial (ZMod p)}
    (hg : g ≠ 0) : k2PolyNagaoWide_nu (f % g) < k2PolyNagaoWide_nu g := by
  unfold k2PolyNagaoWide_nu
  rw [if_neg hg]
  by_cases h : f % g = 0
  · rw [if_pos h]
    exact Nat.succ_pos _
  · rw [if_neg h]
    exact Nat.succ_lt_succ (Polynomial.natDegree_lt_natDegree h (Polynomial.degree_mod_lt f hg))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_mod_lt

omit [Fintype I] [Fact p.Prime] in
/-- `μ` drops if only the `j`- and `m`-coordinates change and their weighted `ν` drops. -/
theorem k2PolyNagaoWide_mu_lt {K : Finset I} {m j : I} (hj : j ∈ K.erase m)
    {v u : I → Polynomial (ZMod p)} (hu : ∀ i, i ≠ j → i ≠ m → u i = v i)
    (h : 2 * k2PolyNagaoWide_nu (u j) + k2PolyNagaoWide_nu (u m) <
      2 * k2PolyNagaoWide_nu (v j) + k2PolyNagaoWide_nu (v m)) :
    k2PolyNagaoWide_mu K m u < k2PolyNagaoWide_mu K m v := by
  have e1 : k2PolyNagaoWide_nu (u j) + ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (u i) =
      ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (u i) :=
    Finset.add_sum_erase (K.erase m) (fun i => k2PolyNagaoWide_nu (u i)) hj
  have e2 : k2PolyNagaoWide_nu (v j) + ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (v i) =
      ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (v i) :=
    Finset.add_sum_erase (K.erase m) (fun i => k2PolyNagaoWide_nu (v i)) hj
  have hs : ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (u i) =
      ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (v i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hu i (Finset.ne_of_mem_erase hi)
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))]
  unfold k2PolyNagaoWide_mu
  rw [← e1, ← e2, hs]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_mu_lt

omit [Fact p.Prime] in
/-- A single root element leaves every coordinate other than its row alone. -/
theorem k2PolyNagaoWide_act_x_ne {i j : I} (hij : i ≠ j) (c : Polynomial (ZMod p))
    (v : I → Polynomial (ZMod p)) {k : I} (hk : k ≠ i) : act (x i j hij c) v k = v k := by
  rw [act_x_apply, if_neg hk, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_act_x_ne

/-- **One Euclidean move** in `S_K` lowers `μ`, as long as some `J`-coordinate is nonzero. -/
theorem k2PolyNagaoWide_step {K : Finset I} {m j : I} (hmK : m ∈ K) (hj : j ∈ K.erase m)
    {v : I → Polynomial (ZMod p)} (hf : v j ≠ 0) :
    ∃ s ∈ k2PolyDeg_S p K, k2PolyNagaoWide_mu K m (act s v) < k2PolyNagaoWide_mu K m v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hS : ∀ {a b : I} (hab : a ≠ b) (c : Polynomial (ZMod p)), a ∈ K → b ∈ K →
      x a b hab c ∈ k2PolyDeg_S p K := fun hab c ha hb =>
    x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hab c ⟨ha, hb⟩
  by_cases hm0 : v m = 0
  · have hf0 := k2PolyNagaoWide_nu_pos hf
    refine ⟨x j m hjm (-1) * x m j hjm.symm 1,
      Subgroup.mul_mem _ (hS hjm _ hjK hmK) (hS hjm.symm _ hmK hjK), ?_⟩
    refine k2PolyNagaoWide_mu_lt hj (fun i hij him => ?_) ?_
    · rw [act_mul, k2PolyNagaoWide_act_x_ne _ _ _ hij, k2PolyNagaoWide_act_x_ne _ _ _ him]
    · have e1 : act (x j m hjm (-1) * x m j hjm.symm 1) v j = 0 := by
        rw [act_mul, act_x_apply, act_x_apply, act_x_apply, if_neg hjm, if_pos rfl, if_pos rfl,
          hm0]
        ring
      have e2 : act (x j m hjm (-1) * x m j hjm.symm 1) v m = v j := by
        rw [act_mul, k2PolyNagaoWide_act_x_ne _ _ _ hjm.symm, act_x_apply, if_pos rfl, hm0]
        ring
      rw [e1, e2, hm0, k2PolyNagaoWide_nu_zero]
      omega
  · by_cases hle : k2PolyNagaoWide_nu (v m) ≤ k2PolyNagaoWide_nu (v j)
    · refine ⟨x j m hjm (-(v j / v m)), hS hjm _ hjK hmK, ?_⟩
      refine k2PolyNagaoWide_mu_lt hj (fun i hij _ => k2PolyNagaoWide_act_x_ne _ _ _ hij) ?_
      have e1 : act (x j m hjm (-(v j / v m))) v j = v j % v m := by
        rw [act_x_apply, if_pos rfl]
        linear_combination -(EuclideanDomain.div_add_mod (v j) (v m))
      rw [e1, k2PolyNagaoWide_act_x_ne _ _ _ hjm.symm]
      have hlt := k2PolyNagaoWide_nu_mod_lt (v j) hm0
      omega
    · refine ⟨x m j hjm.symm (-(v m / v j)), hS hjm.symm _ hmK hjK, ?_⟩
      refine k2PolyNagaoWide_mu_lt hj (fun i _ him => k2PolyNagaoWide_act_x_ne _ _ _ him) ?_
      have e1 : act (x m j hjm.symm (-(v m / v j))) v m = v m % v j := by
        rw [act_x_apply, if_pos rfl]
        linear_combination -(EuclideanDomain.div_add_mod (v m) (v j))
      rw [e1, k2PolyNagaoWide_act_x_ne _ _ _ hjm]
      have hlt := k2PolyNagaoWide_nu_mod_lt (v m) hf
      omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_step

/-- **Clearing `J`.**  Some `s ∈ S_K` kills every `J`-coordinate (strong induction on `μ`). -/
theorem k2PolyNagaoWide_clear {K : Finset I} {m : I} (hmK : m ∈ K) (n : ℕ) :
    ∀ v : I → Polynomial (ZMod p), k2PolyNagaoWide_mu K m v = n →
      ∃ s ∈ k2PolyDeg_S p K, ∀ j ∈ K.erase m, act s v j = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hex : ∃ j ∈ K.erase m, v j ≠ 0
    · obtain ⟨j, hj, hf⟩ := hex
      obtain ⟨s₁, hs₁, hlt⟩ := k2PolyNagaoWide_step hmK hj hf
      obtain ⟨s, hs, hJ⟩ := ih _ (by rw [← hv]; exact hlt) (act s₁ v) rfl
      refine ⟨s * s₁, Subgroup.mul_mem _ hs hs₁, fun i hi => ?_⟩
      rw [act_mul]
      exact hJ i hi
    · push Not at hex
      exact ⟨1, Subgroup.one_mem _, fun j hj => by rw [act_one]; exact hex j hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_clear

/-- **Representatives.**  Every `v ∈ G e_L` is `q r` with `q ∈ Q` and `r` supported on
`{m, L}`. -/
theorem k2PolyNagaoWide_rep_exists {K : Finset I} {m L : I} (hmK : m ∈ K)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    ∃ q ∈ k2PolyNF_Q p K L, ∃ r, k2PolyNagaoWide_Supp m L r ∧ act q r = v := by
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨s, hs, hJ⟩ := k2PolyNagaoWide_clear hmK _ (act y (unitVec L)) rfl
  refine ⟨s⁻¹, Subgroup.mem_sup_left (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L)
    (Subgroup.inv_mem _ hs), act s (act y (unitVec L)), fun i him hiL => ?_, ?_⟩
  · by_cases hiK : i ∈ K
    · exact hJ i (Finset.mem_erase.2 ⟨him, hiK⟩)
    · have hiK' : i ∉ insert L K := fun h => (Finset.mem_insert.1 h).elim hiL hiK
      rw [act_apply_of_rootSpan (p := fun a b => a ∈ K ∧ b ∈ K) (k := i)
          (fun a _ hq e => hiK (by rw [← e]; exact hq.1)) hs,
        act_apply_of_rootSpan (p := fun a b => a ∈ insert L K ∧ b ∈ insert L K) (k := i)
          (fun a _ hq e => hiK' (by rw [← e]; exact hq.1)) hy, unitVec_apply, if_neg hiL]
  · rw [← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_rep_exists

end GroupApproximation.BooneHigman.Metabelian.ElemFP
