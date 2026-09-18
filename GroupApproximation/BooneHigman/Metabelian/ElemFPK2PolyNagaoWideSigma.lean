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
  k2PolyNagaoWide_qsel p K m L v * k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L v)

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
  exact Classical.epsilon_spec ⟨r, hr, q, hq, e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_rep_spec

/-- On the orbit, `q_v ∈ Q` and `q_v r_v = v`. -/
theorem k2PolyNagaoWide_qsel_spec {K : Finset I} {m L : I} (hmK : m ∈ K)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    k2PolyNagaoWide_qsel p K m L v ∈ k2PolyNF_Q p K L ∧
      act (k2PolyNagaoWide_qsel p K m L v) (k2PolyNagaoWide_rep p K m L v) = v :=
  Classical.epsilon_spec (k2PolyNagaoWide_rep_spec hmK hv).2

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

end GroupApproximation.BooneHigman.Metabelian.ElemFP
