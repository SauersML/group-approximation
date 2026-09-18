import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideEuclid
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 4: the section `σ` and its `Q`-equivariance

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyNagaoWideStab`; `J = K \ {m}`, `σ₀ = pair`.

* `k2PolyNagaoWide_rep K m L v`: a representative `r` of `v`, supported on `{m, L}`, with
  `q r = v` for some `q ∈ Q` (chosen by `Classical.epsilon`; exists on the orbit by the
  Euclidean reduction `k2PolyNagaoWide_rep_exists`).  It depends only on the `Q`-orbit of `v`.
* `k2PolyNagaoWide_sigma K m L v = q_v · σ₀(r_v)`.
* `k2PolyNagaoWide_check_Q`: given `Stab(J, m)`, the check of `σ` holds at **every** `g ∈ Q`:
  `(σ(g v))⁻¹ g σ(v) = σ₀(r)⁻¹ t σ₀(r)` with `t = q_{gv}⁻¹ g q_v ∈ Q` fixing `r`, then
  `k2PolyNagaoWide_core`.
* `k2PolyNagaoWide_gens_of_check`: hence every check of `k2PolyNagao_Gens` except the single
  one at `x_mL(1)` holds.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one unitVec x_mem_rootSpan rootSpan_mono)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- The admissible representatives of `v`: supported on `{m, L}` and in the `Q`-orbit of `v`. -/
def k2PolyNagaoWide_repSet (K : Finset I) (m L : I) (v : I → Polynomial (ZMod p))
    (r : I → Polynomial (ZMod p)) : Prop :=
  k2PolyNagaoWide_Supp m L r ∧ ∃ q ∈ k2PolyNF_Q p K L, act q r = v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_repSet

/-- The chosen representative of `v`. -/
noncomputable def k2PolyNagaoWide_rep (K : Finset I) (m L : I) (v : I → Polynomial (ZMod p)) :
    I → Polynomial (ZMod p) :=
  Classical.epsilon (k2PolyNagaoWide_repSet p K m L v)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_rep

/-- The chosen `q ∈ Q` with `q r_v = v`. -/
noncomputable def k2PolyNagaoWide_qsel (K : Finset I) (m L : I) (v : I → Polynomial (ZMod p)) :
    SteinbergGroup I (Polynomial (ZMod p)) :=
  Classical.epsilon fun q => q ∈ k2PolyNF_Q p K L ∧ act q (k2PolyNagaoWide_rep p K m L v) = v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_qsel

/-- **The section.**  `σ(v) = q_v · σ₀(r_v)`. -/
noncomputable def k2PolyNagaoWide_sigma (K : Finset I) (m L : I) (hmL : m ≠ L)
    (v : I → Polynomial (ZMod p)) : SteinbergGroup I (Polynomial (ZMod p)) :=
  k2PolyNagaoWide_qsel p K m L v *
    k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_sigma

end Defs

variable {p : ℕ} [Fact p.Prime]

/-- `Q ≤ G`. -/
theorem k2PolyNagaoWide_Q_le_G (K : Finset I) (L : I) :
    k2PolyNF_Q p K L ≤ k2PolyDeg_G p K L := fun _ hg =>
  rootSpan_mono (p := fun i j => i ∈ insert L K ∧ j ∈ K)
    (q := fun i j => i ∈ insert L K ∧ j ∈ insert L K)
    (fun _ _ _ hij => ⟨hij.1, Finset.mem_insert_of_mem hij.2⟩) (k2PolyNagaoWide_Q_le_Qr K L hg)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Q_le_G

omit [Fact p.Prime] in
/-- `g r = w` gives `g⁻¹ w = r`. -/
theorem k2PolyNagaoWide_act_inv {g : SteinbergGroup I (Polynomial (ZMod p))}
    {r w : I → Polynomial (ZMod p)} (h : act g r = w) : act g⁻¹ w = r := by
  rw [← h, ← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_act_inv

/-- On the orbit, the chosen representative is admissible. -/
theorem k2PolyNagaoWide_rep_spec {K : Finset I} {m L : I} (hmK : m ∈ K)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    k2PolyNagaoWide_repSet p K m L v (k2PolyNagaoWide_rep p K m L v) := by
  obtain ⟨q, hq, r, hr, e⟩ := k2PolyNagaoWide_rep_exists hmK hv
  exact Classical.epsilon_spec (p := k2PolyNagaoWide_repSet p K m L v) ⟨r, hr, q, hq, e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_rep_spec

/-- On the orbit, `q_v ∈ Q` and `q_v r_v = v`. -/
theorem k2PolyNagaoWide_qsel_spec {K : Finset I} {m L : I} (hmK : m ∈ K)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    k2PolyNagaoWide_qsel p K m L v ∈ k2PolyNF_Q p K L ∧
      act (k2PolyNagaoWide_qsel p K m L v) (k2PolyNagaoWide_rep p K m L v) = v :=
  Classical.epsilon_spec
    (p := fun q => q ∈ k2PolyNF_Q p K L ∧ act q (k2PolyNagaoWide_rep p K m L v) = v)
    (k2PolyNagaoWide_rep_spec hmK hv).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_qsel_spec

/-- The admissible set depends only on the `Q`-orbit. -/
theorem k2PolyNagaoWide_repSet_act {K : Finset I} {m L : I}
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p K L)
    (v : I → Polynomial (ZMod p)) :
    k2PolyNagaoWide_repSet p K m L (act g v) = k2PolyNagaoWide_repSet p K m L v := by
  funext r
  apply propext
  unfold k2PolyNagaoWide_repSet
  constructor
  · rintro ⟨hr, q, hq, e⟩
    refine ⟨hr, g⁻¹ * q, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hq, ?_⟩
    rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]
  · rintro ⟨hr, q, hq, e⟩
    exact ⟨hr, g * q, Subgroup.mul_mem _ hg hq, by rw [act_mul, e]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_repSet_act

/-- The chosen representative depends only on the `Q`-orbit. -/
theorem k2PolyNagaoWide_rep_act {K : Finset I} {m L : I}
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p K L)
    (v : I → Polynomial (ZMod p)) :
    k2PolyNagaoWide_rep p K m L (act g v) = k2PolyNagaoWide_rep p K m L v := by
  unfold k2PolyNagaoWide_rep
  rw [k2PolyNagaoWide_repSet_act hg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_rep_act

/-- **`Q`-equivariance.**  Given `Stab(J, m)`, the check of `σ` holds at every `g ∈ Q`. -/
theorem k2PolyNagaoWide_check_Q {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p K L) :
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL) g := by
  intro v hv
  have hv' := k2PolyNF_orbit_act (k2PolyNagaoWide_Q_le_G K L hg) hv
  have hr := k2PolyNagaoWide_rep_spec (m := m) hmK hv
  have hq := k2PolyNagaoWide_qsel_spec (m := m) hmK hv
  have hq' := k2PolyNagaoWide_qsel_spec (m := m) hmK hv'
  have e : k2PolyNagaoWide_rep p K m L (act g v) = k2PolyNagaoWide_rep p K m L v :=
    k2PolyNagaoWide_rep_act hg v
  rw [e] at hq'
  have ht : (k2PolyNagaoWide_qsel p K m L (act g v))⁻¹ * g * k2PolyNagaoWide_qsel p K m L v ∈
      k2PolyNF_Q p K L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq'.1) hg) hq.1
  have htr : act ((k2PolyNagaoWide_qsel p K m L (act g v))⁻¹ * g *
      k2PolyNagaoWide_qsel p K m L v) (k2PolyNagaoWide_rep p K m L v) =
      k2PolyNagaoWide_rep p K m L v := by
    rw [act_mul, act_mul, hq.2]
    exact k2PolyNagaoWide_act_inv hq'.2
  have h := k2PolyNagaoWide_core hmL hmK hLK hthird hStab hr.1 ht htr
  unfold k2PolyNagaoWide_sigma
  rw [e]
  have e2 : (k2PolyNagaoWide_qsel p K m L (act g v) *
        k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v))⁻¹ * g *
      (k2PolyNagaoWide_qsel p K m L v *
        k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v)) =
      (k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v))⁻¹ *
        ((k2PolyNagaoWide_qsel p K m L (act g v))⁻¹ * g * k2PolyNagaoWide_qsel p K m L v) *
        k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v) := by
    group
  rw [e2]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_check_Q

/-- `σ(e_L) ∈ Q`. -/
theorem k2PolyNagaoWide_sigma_unitVec {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) : k2PolyNagaoWide_sigma p K m L hmL (unitVec L) ∈ k2PolyNF_Q p K L := by
  have ho : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = unitVec L :=
    ⟨1, Subgroup.one_mem _, act_one _⟩
  obtain ⟨_, q, hq, e⟩ := k2PolyNagaoWide_rep_spec (m := m) hmK ho
  have hr : k2PolyNagaoWide_rep p K m L (unitVec L) = unitVec L :=
    (k2PolyNagaoWide_act_inv e).symm.trans (k2PolyNF_Q_fix hLK (Subgroup.inv_mem _ hq))
  unfold k2PolyNagaoWide_sigma
  rw [hr, k2PolyNagaoSigma_sigma_unitVec, mul_one]
  exact (k2PolyNagaoWide_qsel_spec (m := m) hmK ho).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_sigma_unitVec

/-- **All checks but one.**  Given `Stab(J, m)` and the single check at `x_mL(1)`, `σ`
passes every check of `k2PolyNagao_Gens`: the others are at elements of `Q`. -/
theorem k2PolyNagaoWide_gens_of_check {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    (hres : k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p)))) :
    k2PolyNagao_Gens p K L (k2PolyNagaoWide_sigma p K m L hmL) m hmL := by
  have hQ : ∀ g ∈ k2PolyNF_Q p K L,
      k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL) g :=
    fun _ hg => k2PolyNagaoWide_check_Q hmL hmK hLK hthird hStab hg
  have hSQ : ∀ {a b : I} (hab : a ≠ b), a ∈ K → b ∈ K →
      x a b hab (1 : Polynomial (ZMod p)) ∈ k2PolyNF_Q p K L := fun hab ha hb =>
    Subgroup.mem_sup_left (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L)
      (x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hab 1 ⟨ha, hb⟩)
  exact ⟨fun _ him hi => ⟨hQ _ (hSQ him hi hmK), hQ _ (hSQ him.symm hmK hi)⟩, hres,
    hQ _ (k2PolyNagaoSigma_x_mem_Q hmL hmK _), hQ _ (k2PolyNagaoSigma_x_mem_Q hmL hmK _),
    fun _ _ => hQ _ (k2PolyNagaoSigma_x_mem_Q hmL hmK _)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_gens_of_check

end GroupApproximation.BooneHigman.Metabelian.ElemFP
