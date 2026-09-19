import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: Euclidean clearing of the `J`-coordinates

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93l's `ElemFPK2PolyNagaoWideEuclid`.
Nothing here depends on the field beyond Euclidean division in `F[X]`.

* `fnWide_nu f = natDegree f + 1` (`0` at `0`); `fnWide_mu K m v = 2 ∑_{j ∈ J} ν(v j) + ν(v m)`.
* `fnWide_step`: one Euclidean move in `S_K` lowers `μ` while some `J`-coordinate is nonzero.
* `fnWide_clear`: some `s ∈ S_K` kills every `J`-coordinate.
* `fnWide_rep_exists`: every orbit vector `v` is `q r` with `q ∈ Q` and `r` supported on `{m, L}`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one act_x_apply unitVec unitVec_apply x_mem_rootSpan act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

open Classical in
/-- `ν f = natDegree f + 1` for `f ≠ 0`, and `ν 0 = 0`. -/
noncomputable def fnWide_nu (f : Polynomial F) : ℕ :=
  if f = 0 then 0 else f.natDegree + 1

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_nu

/-- `μ v = 2 ∑_{j ∈ K \ {m}} ν(v j) + ν(v m)`. -/
noncomputable def fnWide_mu (K : Finset I) (m : I) (v : I → Polynomial F) : ℕ :=
  2 * ∑ i ∈ K.erase m, fnWide_nu (v i) + fnWide_nu (v m)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_mu

theorem fnWide_nu_zero : fnWide_nu (0 : Polynomial F) = 0 := by
  unfold fnWide_nu
  rw [if_pos rfl]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_nu_zero

theorem fnWide_nu_pos {f : Polynomial F} (hf : f ≠ 0) : 0 < fnWide_nu f := by
  unfold fnWide_nu
  rw [if_neg hf]
  exact Nat.succ_pos _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_nu_pos

/-- `ν(f % g) < ν g` for `g ≠ 0`. -/
theorem fnWide_nu_mod_lt (f : Polynomial F) {g : Polynomial F} (hg : g ≠ 0) :
    fnWide_nu (f % g) < fnWide_nu g := by
  unfold fnWide_nu
  rw [if_neg hg]
  by_cases h : f % g = 0
  · rw [if_pos h]
    exact Nat.succ_pos _
  · rw [if_neg h]
    exact Nat.succ_lt_succ (Polynomial.natDegree_lt_natDegree h (Polynomial.degree_mod_lt f hg))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_nu_mod_lt

omit [Fintype I] in
/-- `μ` drops if only the `j`- and `m`-coordinates change and their weighted `ν` drops. -/
theorem fnWide_mu_lt {K : Finset I} {m j : I} (hj : j ∈ K.erase m) {v u : I → Polynomial F}
    (hu : ∀ i, i ≠ j → i ≠ m → u i = v i)
    (h : 2 * fnWide_nu (u j) + fnWide_nu (u m) < 2 * fnWide_nu (v j) + fnWide_nu (v m)) :
    fnWide_mu K m u < fnWide_mu K m v := by
  have e1 : fnWide_nu (u j) + ∑ i ∈ (K.erase m).erase j, fnWide_nu (u i) =
      ∑ i ∈ K.erase m, fnWide_nu (u i) :=
    Finset.add_sum_erase (K.erase m) (fun i => fnWide_nu (u i)) hj
  have e2 : fnWide_nu (v j) + ∑ i ∈ (K.erase m).erase j, fnWide_nu (v i) =
      ∑ i ∈ K.erase m, fnWide_nu (v i) :=
    Finset.add_sum_erase (K.erase m) (fun i => fnWide_nu (v i)) hj
  have hs : ∑ i ∈ (K.erase m).erase j, fnWide_nu (u i) =
      ∑ i ∈ (K.erase m).erase j, fnWide_nu (v i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hu i (Finset.ne_of_mem_erase hi)
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))]
  unfold fnWide_mu
  rw [← e1, ← e2, hs]
  omega

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_mu_lt

/-- A single root element leaves every coordinate other than its row alone. -/
theorem fnWide_act_x_ne {i j : I} (hij : i ≠ j) (c : Polynomial F) (v : I → Polynomial F)
    {k : I} (hk : k ≠ i) : act (x i j hij c) v k = v k := by
  rw [act_x_apply, if_neg hk, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_act_x_ne

/-- **One Euclidean move** in `S_K` lowers `μ`, as long as some `J`-coordinate is nonzero. -/
theorem fnWide_step {K : Finset I} {m j : I} (hmK : m ∈ K) (hj : j ∈ K.erase m)
    {v : I → Polynomial F} (hf : v j ≠ 0) :
    ∃ s ∈ fnS F K, fnWide_mu K m (act s v) < fnWide_mu K m v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hS : ∀ {a b : I} (hab : a ≠ b) (c : Polynomial F), a ∈ K → b ∈ K →
      x a b hab c ∈ fnS F K := fun hab c ha hb =>
    x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hab c ⟨ha, hb⟩
  by_cases hm0 : v m = 0
  · have hf0 := fnWide_nu_pos hf
    refine ⟨x j m hjm (-1) * x m j hjm.symm 1,
      Subgroup.mul_mem _ (hS hjm _ hjK hmK) (hS hjm.symm _ hmK hjK), ?_⟩
    refine fnWide_mu_lt hj (fun i hij him => ?_) ?_
    · rw [act_mul, fnWide_act_x_ne _ _ _ hij, fnWide_act_x_ne _ _ _ him]
    · have e1 : act (x j m hjm (-1) * x m j hjm.symm 1) v j = 0 := by
        rw [act_mul, act_x_apply, act_x_apply, act_x_apply, if_neg hjm, if_pos rfl, if_pos rfl,
          hm0]
        ring
      have e2 : act (x j m hjm (-1) * x m j hjm.symm 1) v m = v j := by
        rw [act_mul, fnWide_act_x_ne _ _ _ hjm.symm, act_x_apply, if_pos rfl, hm0]
        ring
      rw [e1, e2, hm0, fnWide_nu_zero]
      omega
  · by_cases hle : fnWide_nu (v m) ≤ fnWide_nu (v j)
    · refine ⟨x j m hjm (-(v j / v m)), hS hjm _ hjK hmK, ?_⟩
      refine fnWide_mu_lt hj (fun i hij _ => fnWide_act_x_ne _ _ _ hij) ?_
      have e1 : act (x j m hjm (-(v j / v m))) v j = v j % v m := by
        rw [act_x_apply, if_pos rfl]
        linear_combination -(EuclideanDomain.div_add_mod (v j) (v m))
      rw [e1, fnWide_act_x_ne _ _ _ hjm.symm]
      have hlt := fnWide_nu_mod_lt (v j) hm0
      omega
    · refine ⟨x m j hjm.symm (-(v m / v j)), hS hjm.symm _ hmK hjK, ?_⟩
      refine fnWide_mu_lt hj (fun i _ him => fnWide_act_x_ne _ _ _ him) ?_
      have e1 : act (x m j hjm.symm (-(v m / v j))) v m = v m % v j := by
        rw [act_x_apply, if_pos rfl]
        linear_combination -(EuclideanDomain.div_add_mod (v m) (v j))
      rw [e1, fnWide_act_x_ne _ _ _ hjm]
      have hlt := fnWide_nu_mod_lt (v m) hf
      omega

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_step

/-- **Clearing `J`.** Some `s ∈ S_K` kills every `J`-coordinate (strong induction on `μ`). -/
theorem fnWide_clear {K : Finset I} {m : I} (hmK : m ∈ K) (n : ℕ) :
    ∀ v : I → Polynomial F, fnWide_mu K m v = n →
      ∃ s ∈ fnS F K, ∀ j ∈ K.erase m, act s v j = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hex : ∃ j ∈ K.erase m, v j ≠ 0
    · obtain ⟨j, hj, hf⟩ := hex
      obtain ⟨s₁, hs₁, hlt⟩ := fnWide_step hmK hj hf
      obtain ⟨s, hs, hJ⟩ := ih _ (by rw [← hv]; exact hlt) (act s₁ v) rfl
      refine ⟨s * s₁, Subgroup.mul_mem _ hs hs₁, fun i hi => ?_⟩
      rw [act_mul]
      exact hJ i hi
    · push Not at hex
      exact ⟨1, Subgroup.one_mem _, fun j hj => by rw [act_one]; exact hex j hj⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_clear

/-- **Representatives.** Every `v ∈ S_{K ∪ {L}} e_L` is `q r` with `q ∈ Q` and `r` supported on
`{m, L}`. -/
theorem fnWide_rep_exists {K : Finset I} {m L : I} (hmK : m ∈ K) {v : I → Polynomial F}
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    ∃ q ∈ fnQ F K L, ∃ r, fnWide_Supp m L r ∧ act q r = v := by
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨s, hs, hJ⟩ := fnWide_clear hmK _ (act y (unitVec L)) rfl
  refine ⟨s⁻¹, Subgroup.mem_sup_left (S := fnS F K) (T := fnV F K L)
    (Subgroup.inv_mem _ hs), act s (act y (unitVec L)), fun i him hiL => ?_, ?_⟩
  · by_cases hiK : i ∈ K
    · exact hJ i (Finset.mem_erase.2 ⟨him, hiK⟩)
    · have hiK' : i ∉ insert L K := fun h => (Finset.mem_insert.1 h).elim hiL hiK
      rw [act_apply_of_rootSpan (p := fun a b => a ∈ K ∧ b ∈ K) (k := i)
          (fun a _ hq e => hiK (by rw [← e]; exact hq.1)) hs,
        act_apply_of_rootSpan (p := fun a b => a ∈ insert L K ∧ b ∈ insert L K) (k := i)
          (fun a _ hq e => hiK' (by rw [← e]; exact hq.1)) hy, unitVec_apply, if_neg hiL]
  · rw [← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_rep_exists

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
