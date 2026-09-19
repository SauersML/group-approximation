import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideEuclid
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: the wide section and its checks at `Q`

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93l's `ElemFPK2PolyNagaoWideSigma`.
Notation of `FieldNF.WideDefs`: `σ(v) = q_v · σ₀(r_v)` (`fnWide_sigma`).

* `fnWide_rep_spec`, `fnWide_qsel_spec`: on the orbit, `r_v` is admissible, `q_v ∈ Q` and
  `q_v r_v = v`; `fnWide_rep_act`: `r_v` depends only on the `Q`-orbit of `v`.
* `fnWide_check_Q`: given `Stab(J, m)`, the check of `σ` holds at every element of `Q`, with
  target `Z ⊔ Q` (via `fnWide_core`).
* `fnWide_sigma_unitVec`: `σ(e_L) ∈ Z ⊔ Q`.
* `fnWide_gens_of_check`: given `Stab(J, m)` and the single check at `x_mL(1)`, `σ` is good on
  the whole small generating set (`fnGenGood`).
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one unitVec unitVec_apply x_mem_rootSpan rootSpan_mono act_eq_self_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- `Q` fixes `e_L`. -/
theorem fnQ_fix {K : Finset I} {L : I} (hLK : L ∉ K) {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnQ F K L) : act g (unitVec L) = unitVec L := by
  obtain ⟨s, hs, v, hv, rfl⟩ := fn_SV_decomp hLK hg
  have hfix : ∀ j : I, j ∈ K → unitVec (R := Polynomial F) L j = 0 := fun j hj => by
    rw [unitVec_apply, if_neg (fun e => hLK (e ▸ hj))]
  have hS : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hs
  have hV : act v (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hv
  rw [act_mul, hV, hS]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnQ_fix

/-- `Q ≤ S_{K ∪ {L}}`. -/
theorem fnWide_Q_le_G (K : Finset I) (L : I) : fnQ F K L ≤ fnS F (insert L K) := fun _ hg =>
  rootSpan_mono (p := fun i j => i ∈ insert L K ∧ j ∈ K)
    (q := fun i j => i ∈ insert L K ∧ j ∈ insert L K)
    (fun _ _ _ hij => ⟨hij.1, Finset.mem_insert_of_mem hij.2⟩) (fnWide_Q_le_Qr K L hg)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Q_le_G

/-- `g r = w` gives `g⁻¹ w = r`. -/
theorem fnWide_act_inv {g : SteinbergGroup I (Polynomial F)} {r w : I → Polynomial F}
    (h : act g r = w) : act g⁻¹ w = r := by
  rw [← h, ← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_act_inv

/-- On the orbit, the chosen representative is admissible. -/
theorem fnWide_rep_spec {K : Finset I} {m L : I} (hmK : m ∈ K) {v : I → Polynomial F}
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    fnWide_repSet F K m L v (fnWide_rep F K m L v) := by
  obtain ⟨q, hq, r, hr, e⟩ := fnWide_rep_exists hmK hv
  exact Classical.epsilon_spec (p := fnWide_repSet F K m L v) ⟨r, hr, q, hq, e⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_rep_spec

/-- On the orbit, `q_v ∈ Q` and `q_v r_v = v`. -/
theorem fnWide_qsel_spec {K : Finset I} {m L : I} (hmK : m ∈ K) {v : I → Polynomial F}
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    fnWide_qsel F K m L v ∈ fnQ F K L ∧ act (fnWide_qsel F K m L v) (fnWide_rep F K m L v) = v :=
  Classical.epsilon_spec (p := fun q => q ∈ fnQ F K L ∧ act q (fnWide_rep F K m L v) = v)
    (fnWide_rep_spec hmK hv).2

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_qsel_spec

/-- The admissible set depends only on the `Q`-orbit. -/
theorem fnWide_repSet_act {K : Finset I} {m L : I} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnQ F K L) (v : I → Polynomial F) :
    fnWide_repSet F K m L (act g v) = fnWide_repSet F K m L v := by
  funext r
  apply propext
  unfold fnWide_repSet
  constructor
  · rintro ⟨hr, q, hq, e⟩
    refine ⟨hr, g⁻¹ * q, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hq, ?_⟩
    rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]
  · rintro ⟨hr, q, hq, e⟩
    exact ⟨hr, g * q, Subgroup.mul_mem _ hg hq, by rw [act_mul, e]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_repSet_act

/-- The chosen representative depends only on the `Q`-orbit. -/
theorem fnWide_rep_act {K : Finset I} {m L : I} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnQ F K L) (v : I → Polynomial F) :
    fnWide_rep F K m L (act g v) = fnWide_rep F K m L v := by
  unfold fnWide_rep
  rw [fnWide_repSet_act hg]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_rep_act

/-- **`Q`-equivariance.** Given `Stab(J, m)`, the check of `σ` holds at every `g ∈ Q`. -/
theorem fnWide_check_Q {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (hStab : fnWide_Stab F (K.erase m) m)
    {g : SteinbergGroup I (Polynomial F)} (hg : g ∈ fnQ F K L) :
    fnCheck F K L (fnWide_sigma F K m L hmL) g := by
  intro v hv
  have hv' := fn_orbit_act (fnWide_Q_le_G K L hg) hv
  have hr := fnWide_rep_spec (m := m) hmK hv
  have hq := fnWide_qsel_spec (m := m) hmK hv
  have hq' := fnWide_qsel_spec (m := m) hmK hv'
  have e : fnWide_rep F K m L (act g v) = fnWide_rep F K m L v := fnWide_rep_act hg v
  rw [e] at hq'
  have ht : (fnWide_qsel F K m L (act g v))⁻¹ * g * fnWide_qsel F K m L v ∈ fnQ F K L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq'.1) hg) hq.1
  have htr : act ((fnWide_qsel F K m L (act g v))⁻¹ * g * fnWide_qsel F K m L v)
      (fnWide_rep F K m L v) = fnWide_rep F K m L v := by
    rw [act_mul, act_mul, hq.2]
    exact fnWide_act_inv hq'.2
  have h := fnWide_core hmL hmK hLK hthird hStab hr.1 ht htr
  unfold fnWide_sigma
  rw [e]
  have e2 : (fnWide_qsel F K m L (act g v) *
        fnSigma_sigma F m L hmL (fnWide_rep F K m L v))⁻¹ * g *
      (fnWide_qsel F K m L v * fnSigma_sigma F m L hmL (fnWide_rep F K m L v)) =
      (fnSigma_sigma F m L hmL (fnWide_rep F K m L v))⁻¹ *
        ((fnWide_qsel F K m L (act g v))⁻¹ * g * fnWide_qsel F K m L v) *
        fnSigma_sigma F m L hmL (fnWide_rep F K m L v) := by
    group
  rw [e2]
  exact h

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_check_Q

/-- `σ(e_L) ∈ Q`, hence `∈ Z ⊔ Q`. -/
theorem fnWide_sigma_unitVec {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) : fnWide_sigma F K m L hmL (unitVec L) ∈ fnZQ F K L := by
  have ho : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = unitVec L :=
    ⟨1, Subgroup.one_mem _, act_one _⟩
  obtain ⟨_, q, hq, e⟩ := fnWide_rep_spec (m := m) hmK ho
  have hr : fnWide_rep F K m L (unitVec L) = unitVec L :=
    (fnWide_act_inv e).symm.trans (fnQ_fix hLK (Subgroup.inv_mem _ hq))
  unfold fnWide_sigma
  rw [hr, fnSigma_sigma_unitVec, mul_one]
  exact fn_mem_ZQ_of_mem_Q (fnWide_qsel_spec (m := m) hmK ho).1

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_sigma_unitVec

/-- **All checks but one.** Given `Stab(J, m)` and the single check at `x_mL(1)`, the wide
section is good on the whole small generating set: the other generators lie in `Q`. -/
theorem fnWide_gens_of_check {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (hStab : fnWide_Stab F (K.erase m) m)
    (hres : fnCheck F K L (fnWide_sigma F K m L hmL) (x m L hmL (1 : Polynomial F))) :
    fnGenGood F K L m hmL (fnWide_sigma F K m L hmL) := by
  have hm' : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hL' : L ∈ insert L K := Finset.mem_insert_self L K
  have hxS : ∀ {i j : I} (hij : i ≠ j) (f : Polynomial F), i ∈ insert L K → j ∈ insert L K →
      x i j hij f ∈ fnS F (insert L K) := fun hij f hi hj =>
    x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hij f ⟨hi, hj⟩
  have hQ : ∀ g ∈ fnQ F K L, fnCheck F K L (fnWide_sigma F K m L hmL) g :=
    fun _ hg => fnWide_check_Q hmL hmK hLK hthird hStab hg
  have hSQ : ∀ {a b : I} (hab : a ≠ b) (f : Polynomial F), a ∈ K → b ∈ K →
      x a b hab f ∈ fnQ F K L := fun hab f ha hb =>
    Subgroup.mem_sup_left (S := fnS F K) (T := fnV F K L)
      (x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hab f ⟨ha, hb⟩)
  have hLQ : ∀ f : Polynomial F, x L m hmL.symm f ∈ fnQ F K L := fun f =>
    Subgroup.mem_sup_right (S := fnS F K) (T := fnV F K L)
      (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hmL.symm f ⟨rfl, hmK⟩)
  refine ⟨fun i him hi => ⟨⟨hxS him 1 (Finset.mem_insert_of_mem hi) hm', hQ _ (hSQ him 1 hi hmK)⟩,
    ⟨hxS him.symm 1 hm' (Finset.mem_insert_of_mem hi), hQ _ (hSQ him.symm 1 hmK hi)⟩⟩,
    ⟨hxS hmL 1 hm' hL', hres⟩, fun f => ⟨hxS hmL.symm f hL' hm', hQ _ (hLQ f)⟩⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_gens_of_check

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
