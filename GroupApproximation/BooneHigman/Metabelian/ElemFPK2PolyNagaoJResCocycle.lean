import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual root check, part 1: the check at a general element

Lane `bh-met-94e`.  Notation of `ElemFPK2PolyNagaoJRedMove`: `y = x_mL(1)`,
`σ = k2PolyNagaoWide_sigma`, `Q = S_K ⊔ V`.

* `k2PolyNagaoJRes_Ck p K m L hmL g v`: the check `σ(g v)⁻¹ g σ(v) ∈ Q` of `σ` at the element
  `g` and the vector `v`.  At `g = y` it is `k2PolyNagaoJRed_Chk` (`k2PolyNagaoJRes_Ck_y`).
* `k2PolyNagaoJRes_Ck_mul`: the check is multiplicative (cocycle identity).
* `k2PolyNagaoJRes_Ck_conj`: for `g = A⁻¹ B A`, the checks of `A` at `v` and at `g v` and of
  `B` at `A v` give the check of `g` at `v`.
* `k2PolyNagaoJRes_Ck_Q`: every element of `Q` passes the check at every orbit vector
  (`k2PolyNagaoWide_check_Q`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The check of `σ` at the element `g` and the vector `v`. -/
def k2PolyNagaoJRes_Ck (p : ℕ) [Fact p.Prime] (K : Finset I) (m L : I) (hmL : m ≠ L)
    (g : SteinbergGroup I (Polynomial (ZMod p))) (v : I → Polynomial (ZMod p)) : Prop :=
  (k2PolyNagaoWide_sigma p K m L hmL (act g v))⁻¹ * g * k2PolyNagaoWide_sigma p K m L hmL v ∈
    k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck

/-- The group identity behind `k2PolyNagaoJRes_Ck_mul`. -/
theorem k2PolyNagaoJRes_group_mul {G : Type*} [Group G] (g h X Y Z : G) :
    (Z⁻¹ * g * Y) * (Y⁻¹ * h * X) = Z⁻¹ * (g * h) * X := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_group_mul

/-- The group identity behind `k2PolyNagaoJRes_Ck_conj`. -/
theorem k2PolyNagaoJRes_group_conj {G : Type*} [Group G] (A B P X Y Z : G) :
    (P⁻¹ * A * Z)⁻¹ * (P⁻¹ * B * Y) * (Y⁻¹ * A * X) = Z⁻¹ * (A⁻¹ * B * A) * X := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_group_conj

variable {p : ℕ} [Fact p.Prime]

/-- At `g = y = x_mL(1)` the check is `k2PolyNagaoJRed_Chk`. -/
theorem k2PolyNagaoJRes_Ck_y {K : Finset I} {m L : I} (hmL : m ≠ L)
    (v : I → Polynomial (ZMod p)) :
    k2PolyNagaoJRes_Ck p K m L hmL (x m L hmL (1 : Polynomial (ZMod p))) v ↔
      k2PolyNagaoJRed_Chk p K m L hmL v :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_y

/-- **The cocycle identity**: `c(g h, v) = c(g, h v) c(h, v)`. -/
theorem k2PolyNagaoJRes_Ck_mul {K : Finset I} {m L : I} {hmL : m ≠ L}
    {g h : SteinbergGroup I (Polynomial (ZMod p))} {v : I → Polynomial (ZMod p)}
    (hg : k2PolyNagaoJRes_Ck p K m L hmL g (act h v))
    (hh : k2PolyNagaoJRes_Ck p K m L hmL h v) : k2PolyNagaoJRes_Ck p K m L hmL (g * h) v := by
  unfold k2PolyNagaoJRes_Ck at hg hh ⊢
  have key := Subgroup.mul_mem _ hg hh
  rw [k2PolyNagaoJRes_group_mul, ← act_mul] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_mul

/-- **Conjugation.**  For `g = A⁻¹ B A`: `c(g, v) = c(A, g v)⁻¹ c(B, A v) c(A, v)`, since
`A (g v) = B (A v)`. -/
theorem k2PolyNagaoJRes_Ck_conj {K : Finset I} {m L : I} {hmL : m ≠ L}
    {g A B : SteinbergGroup I (Polynomial (ZMod p))} (hg : g = A⁻¹ * B * A)
    {v : I → Polynomial (ZMod p)} (h1 : k2PolyNagaoJRes_Ck p K m L hmL A v)
    (h2 : k2PolyNagaoJRes_Ck p K m L hmL B (act A v))
    (h3 : k2PolyNagaoJRes_Ck p K m L hmL A (act g v)) : k2PolyNagaoJRes_Ck p K m L hmL g v := by
  subst hg
  unfold k2PolyNagaoJRes_Ck at h1 h2 h3 ⊢
  have e : act A (act (A⁻¹ * B * A) v) = act B (act A v) := by
    rw [← act_mul, ← act_mul, show A * (A⁻¹ * B * A) = B * A by group]
  rw [e] at h3
  have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h3) h2) h1
  rw [k2PolyNagaoJRes_group_conj] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_conj

/-- Every element of `Q` passes the check at every orbit vector. -/
theorem k2PolyNagaoJRes_Ck_Q {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    k2PolyNagaoJRes_Ck p K m L hmL q v :=
  k2PolyNagaoWide_check_Q hmL hmK hLK hthird hStab hq v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_Q

end GroupApproximation.BooneHigman.Metabelian.ElemFP
