import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoRootMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The `J`-reduction of the root check, part 1: the cocycle transfer

Lane `bh-met-94a`.  Notation of `ElemFPK2PolyNagaoRootMain`: `y = x_mL(1)`,
`σ = k2PolyNagaoWide_sigma`, `J = K \ {m}`, `Q^m = k2PolyNagaoWide_Qm`.

* `k2PolyNagaoJRed_Chk p K m L hmL v`: the check `σ(y v)⁻¹ y σ(v) ∈ Q` at one orbit vector.
* `k2PolyNagaoJRed_transfer`: for `g ∈ Q^m` and an orbit vector `v`, the check at `g v` gives
  the check at `v`.  The cocycle identity
  `c(y, v) = c(y g y⁻¹, y v)⁻¹ c(y, g v) c(g, v)`
  does this.  The outer factors are in `Q` by `k2PolyNagaoWide_check_Q`, since `g ∈ Q` and
  `y g y⁻¹ ∈ Q^m ≤ Q` (`k2PolyNagaoWide_Gml_conj_Qm`).
* `k2PolyNagaoJRed_x_mem_Qm`, `k2PolyNagaoJRed_orbit_out`: small helpers.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul
  act_x_apply unitVec unitVec_apply x_mem_rootSpan act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The check of `σ` at `y = x_mL(1)` at the single vector `v`. -/
def k2PolyNagaoJRed_Chk (p : ℕ) [Fact p.Prime] (K : Finset I) (m L : I) (hmL : m ≠ L)
    (v : I → Polynomial (ZMod p)) : Prop :=
  (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
      x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
    k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_Chk

/-- The group identity behind the cocycle transfer. -/
theorem k2PolyNagaoJRed_group_id {G : Type*} [Group G] (A B C D X Y : G) :
    (A⁻¹ * (X * Y * X⁻¹) * B)⁻¹ * (A⁻¹ * X * C) * (C⁻¹ * Y * D) = B⁻¹ * X * D := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_group_id

variable {p : ℕ} [Fact p.Prime]

/-- The root `x_ij(a)`, `i ∈ K ∪ {L}`, `j ∈ K \ {m}`, lies in `Q^m`. -/
theorem k2PolyNagaoJRed_x_mem_Qm {K : Finset I} {m L i j : I} (hij : i ≠ j)
    (a : Polynomial (ZMod p)) (hi : i ∈ insert L K) (hj : j ∈ K.erase m) :
    x i j hij a ∈ k2PolyNagaoWide_Qm p K m L :=
  x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_x_mem_Qm

/-- An orbit vector vanishes outside `K ∪ {L}`. -/
theorem k2PolyNagaoJRed_orbit_out {K : Finset I} {L : I} {v : I → Polynomial (ZMod p)}
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) {k : I} (hk : k ∉ insert L K) :
    v k = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have hkL : k ≠ L := fun e => hk (by rw [e]; exact Finset.mem_insert_self L K)
  rw [act_apply_of_rootSpan (p := fun a b => a ∈ insert L K ∧ b ∈ insert L K) (k := k)
      (fun a _ hq e => hk (by rw [← e]; exact hq.1)) hy, unitVec_apply, if_neg hkL]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_orbit_out

/-- **The cocycle transfer.**  For `g ∈ Q^m` and an orbit vector `v`, the check at `g v` gives
the check at `v`: `c(y, v) = c(y g y⁻¹, y v)⁻¹ c(y, g v) c(g, v)`, and the outer factors are
in `Q` (`k2PolyNagaoWide_check_Q` at `g` and at `y g y⁻¹ ∈ Q^m`). -/
theorem k2PolyNagaoJRed_transfer {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNagaoWide_Qm p K m L)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (h : k2PolyNagaoJRed_Chk p K m L hmL (act g v)) : k2PolyNagaoJRed_Chk p K m L hmL v := by
  have hg' : g ∈ k2PolyNF_Q p K L := k2PolyNagaoWide_Qm_le_Q K m L hg
  have hxg : x m L hmL (1 : Polynomial (ZMod p)) * g * (x m L hmL (1 : Polynomial (ZMod p)))⁻¹ ∈
      k2PolyNF_Q p K L :=
    k2PolyNagaoWide_Qm_le_Q K m L (k2PolyNagaoWide_Gml_conj_Qm hmK hLK
      (k2PolyNagaoWide_x_mem_Gml hmL (Or.inl rfl) (Or.inr rfl) _) hg)
  have hxG := k2PolyEuclid_x_mem_G (K := K) hmL (1 : Polynomial (ZMod p))
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)
  have hxv := k2PolyNF_orbit_act hxG hv
  have hxx : act (x m L hmL (1 : Polynomial (ZMod p)))⁻¹
      (act (x m L hmL (1 : Polynomial (ZMod p))) v) = v := k2PolyNagaoWide_act_inv rfl
  have e : act (x m L hmL (1 : Polynomial (ZMod p)) * g * (x m L hmL (1 : Polynomial (ZMod p)))⁻¹)
      (act (x m L hmL (1 : Polynomial (ZMod p))) v) =
      act (x m L hmL (1 : Polynomial (ZMod p))) (act g v) := by
    rw [act_mul, act_mul, hxx]
  have h1 : (k2PolyNagaoWide_sigma p K m L hmL
      (act (x m L hmL (1 : Polynomial (ZMod p))) (act g v)))⁻¹ *
      (x m L hmL (1 : Polynomial (ZMod p)) * g * (x m L hmL (1 : Polynomial (ZMod p)))⁻¹) *
      k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v) ∈
      k2PolyNF_Q p K L := by
    have h1' := k2PolyNagaoWide_check_Q hmL hmK hLK hthird hStab hxg
      (act (x m L hmL (1 : Polynomial (ZMod p))) v) hxv
    rw [e] at h1'
    exact h1'
  have h3 : (k2PolyNagaoWide_sigma p K m L hmL (act g v))⁻¹ * g *
      k2PolyNagaoWide_sigma p K m L hmL v ∈ k2PolyNF_Q p K L :=
    k2PolyNagaoWide_check_Q hmL hmK hLK hthird hStab hg' v hv
  unfold k2PolyNagaoJRed_Chk at h ⊢
  have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h) h3
  rw [k2PolyNagaoJRed_group_id] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_transfer

end GroupApproximation.BooneHigman.Metabelian.ElemFP
