import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The root check of the wide section, part 1: the rank-one orbit of `e_L`

Lane `bh-met-93v`.  Notation of `ElemFPK2PolyNagaoWideStab`; `R = F_p[X]`, `m ≠ L`,
`P(α, β) = α e_m + β e_L`, `W = w_mL(-1)`.

* `k2PolyNagaoRoot_act_xmL`, `_act_xLm`, `_act_W`: the action of `x_mL(a)`, `x_Lm(a)`, `W` on
  `P(α, β)` is `P(α + aβ, β)`, `P(α, β + aα)`, `P(-β, α)`.
* `k2PolyNagaoRoot_orbit_pair`: every coprime `(a, b)` gives `P(a, b) = y e_L` with
  `y ∈ G_{{m}}`: for `a = 0`, `b` is a unit `c⁻¹` and `y = x_mL(-c) x_Lm(b - 1) x_mL(1)`; for
  `a ≠ 0`, `y = x_Lm(b / a) W y'` with `y' e_L = P(b % a, -a)` (induction on `deg a`).
* `k2PolyNagaoRoot_coprime`: a vector of any `G_K`-orbit of `e_L`, supported on `{m, L}`, has
  coprime `(m, L)` coordinates (the `L`-row of `y⁻¹ v = e_L`).
* `k2PolyNagaoRoot_orbit_one`: hence it lies in the `G_{{m}}`-orbit of `e_L`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul
  act_x_apply unitVec unitVec_apply)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

omit [Fintype I] [Fact p.Prime] in
/-- Coordinates of `α e_m + β e_L`. -/
theorem k2PolyNagaoRoot_P_apply (m L : I) (α β : Polynomial (ZMod p)) (k : I) :
    (α • (unitVec m : I → Polynomial (ZMod p)) + β • unitVec L) k =
      (if k = m then α else 0) + (if k = L then β else 0) := by
  simp only [Pi.add_apply, Pi.smul_apply, unitVec_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_P_apply

omit [Fact p.Prime] in
/-- `x_mL(a) P(α, β) = P(α + aβ, β)`. -/
theorem k2PolyNagaoRoot_act_xmL {m L : I} (hmL : m ≠ L) (a α β : Polynomial (ZMod p)) :
    act (x m L hmL a) (α • unitVec m + β • unitVec L) =
      (α + a * β) • unitVec m + β • unitVec L := by
  funext k
  rw [act_x_apply, k2PolyNagaoRoot_P_apply, k2PolyNagaoRoot_P_apply, k2PolyNagaoRoot_P_apply,
    if_neg hmL.symm, if_pos rfl, zero_add]
  split_ifs <;> ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_act_xmL

omit [Fact p.Prime] in
/-- `x_Lm(a) P(α, β) = P(α, β + aα)`. -/
theorem k2PolyNagaoRoot_act_xLm {m L : I} (hmL : m ≠ L) (a α β : Polynomial (ZMod p)) :
    act (x L m hmL.symm a) (α • unitVec m + β • unitVec L) =
      α • unitVec m + (β + a * α) • unitVec L := by
  funext k
  rw [act_x_apply, k2PolyNagaoRoot_P_apply, k2PolyNagaoRoot_P_apply, k2PolyNagaoRoot_P_apply,
    if_pos rfl, if_neg hmL, add_zero]
  split_ifs <;> ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_act_xLm

omit [Fact p.Prime] in
/-- `W P(α, β) = P(-β, α)`. -/
theorem k2PolyNagaoRoot_act_W {m L : I} (hmL : m ≠ L) (α β : Polynomial (ZMod p)) :
    act (w m L hmL (-1 : (Polynomial (ZMod p))ˣ)) (α • unitVec m + β • unitVec L) =
      (-β) • unitVec m + α • unitVec L := by
  have hu : ((-1 : (Polynomial (ZMod p))ˣ) : Polynomial (ZMod p)) = -1 := by
    rw [Units.val_neg, Units.val_one]
  have hui : (((-1 : (Polynomial (ZMod p))ˣ)⁻¹ : (Polynomial (ZMod p))ˣ) :
      Polynomial (ZMod p)) = -1 := by
    rw [inv_neg, inv_one, Units.val_neg, Units.val_one]
  rw [w, act_mul, act_mul, k2PolyNagaoRoot_act_xmL, k2PolyNagaoRoot_act_xLm,
    k2PolyNagaoRoot_act_xmL, hu, hui]
  exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L) (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_act_W

/-- `w_mL(u) ∈ G_{{m}}`. -/
theorem k2PolyNagaoRoot_w_mem {m L : I} (hmL : m ≠ L) (u : (Polynomial (ZMod p))ˣ) :
    w m L hmL u ∈ k2PolyDeg_G p {m} L := by
  have hm : m ∈ insert L ({m} : Finset I) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
  have hL : L ∈ insert L ({m} : Finset I) := Finset.mem_insert_self L {m}
  rw [w]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (k2PolyEuclid_x_mem_G hmL _ hm hL)
    (k2PolyEuclid_x_mem_G hmL.symm _ hL hm)) (k2PolyEuclid_x_mem_G hmL _ hm hL)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_w_mem

/-- **The rank-one orbit.**  Every coprime `(a, b)` gives `a e_m + b e_L = y e_L` with
`y ∈ G_{{m}}` (induction on `deg a`, along the Euclidean recursion of `σ₀`). -/
theorem k2PolyNagaoRoot_orbit_pair {m L : I} (hmL : m ≠ L) (a : Polynomial (ZMod p)) :
    ∀ b : Polynomial (ZMod p), IsCoprime a b →
      ∃ y ∈ k2PolyDeg_G p {m} L, act y (unitVec L) = a • unitVec m + b • unitVec L := by
  induction a using (Polynomial.degree_lt_wf (R := ZMod p)).induction with
  | _ a ih =>
    intro b hab
    have hm : m ∈ insert L ({m} : Finset I) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
    have hL : L ∈ insert L ({m} : Finset I) := Finset.mem_insert_self L {m}
    by_cases ha : a = 0
    · subst ha
      obtain ⟨c, hc⟩ := (isCoprime_zero_left.1 hab).exists_left_inv
      refine ⟨x m L hmL (-c) * x L m hmL.symm (b - 1) * x m L hmL 1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (k2PolyEuclid_x_mem_G hmL _ hm hL)
          (k2PolyEuclid_x_mem_G hmL.symm _ hL hm)) (k2PolyEuclid_x_mem_G hmL _ hm hL), ?_⟩
      have he : (unitVec L : I → Polynomial (ZMod p)) =
          (0 : Polynomial (ZMod p)) • unitVec m + (1 : Polynomial (ZMod p)) • unitVec L := by
        rw [zero_smul, one_smul, zero_add]
      have h0 := k2PolyNagaoRoot_act_xmL hmL (1 : Polynomial (ZMod p)) 0 1
      rw [← he] at h0
      rw [act_mul, act_mul, h0, k2PolyNagaoRoot_act_xLm, k2PolyNagaoRoot_act_xmL]
      exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L)
        (by linear_combination (-1 : Polynomial (ZMod p)) * hc) (by ring)
    · obtain ⟨y, hy, hye⟩ := ih (b % a) (Polynomial.degree_mod_lt b ha) (-a)
        (k2PolyNagaoWeyl_coprime_step hab)
      refine ⟨x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) * y,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (k2PolyEuclid_x_mem_G hmL.symm _ hL hm)
          (k2PolyNagaoRoot_w_mem hmL _)) hy, ?_⟩
      rw [act_mul, act_mul, hye, k2PolyNagaoRoot_act_W, k2PolyNagaoRoot_act_xLm]
      have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
      exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L) (neg_neg a)
        (by linear_combination h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_orbit_pair

/-- A vector of the `G_K`-orbit of `e_L` supported on `{m, L}` has coprime `(m, L)`
coordinates: the `L`-row of `y⁻¹ (v_m e_m + v_L e_L) = e_L`. -/
theorem k2PolyNagaoRoot_coprime {K : Finset I} {m L : I} (hmL : m ≠ L)
    {v : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L v)
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) : IsCoprime (v m) (v L) := by
  obtain ⟨y, _, hy⟩ := hv
  have h1 := k2PolyNF_act_inv hy
  rw [k2PolyNagaoWide_decomp hmL hr, k2PolyNagaoWide_act_lin] at h1
  have h2 := congrFun h1 L
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, unitVec_apply,
    if_pos rfl] at h2
  exact ⟨act y⁻¹ (unitVec m) L, act y⁻¹ (unitVec L) L, by linear_combination h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_coprime

/-- **Orbit transfer.**  A vector of the `G_K`-orbit of `e_L` supported on `{m, L}` lies in
the `G_{{m}}`-orbit of `e_L`. -/
theorem k2PolyNagaoRoot_orbit_one {K : Finset I} {m L : I} (hmL : m ≠ L)
    {v : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L v)
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    ∃ y ∈ k2PolyDeg_G p {m} L, act y (unitVec L) = v := by
  obtain ⟨y, hy, e⟩ :=
    k2PolyNagaoRoot_orbit_pair hmL (v m) (v L) (k2PolyNagaoRoot_coprime hmL hr hv)
  exact ⟨y, hy, e.trans (k2PolyNagaoWide_decomp hmL hr).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_orbit_one

end GroupApproximation.BooneHigman.Metabelian.ElemFP
