import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusConj
import GroupApproximation.Meta.AxiomGuard

/-!
# The odd-`p` Nagao torus, part 2: `T(α, β)` against the Euclidean word

Lane `bh-met-94b`.  With `T(α, β) = t_mL(β)⁻¹ t_mi(α β)` (part 1):

* `k2PolyNagaoTorus_divmod_scale`: `(β b) / (α a) = β α⁻¹ (b / a)`, `(β b) % (α a) = β (b % a)`;
* `k2PolyNagaoTorus_pair_mem`: for coprime `(a, b)`,
  `pair(α a, β b)⁻¹ T(α, β) pair(a, b) ∈ Q` (induction on `deg a`: one Euclidean step
  moves `T(α, β)` past `x'(b / a)` and swaps it to `T(β, α)` across `W`);
* `k2PolyNagaoTorus_pair_mem_one`: the case `β = 1`,
  `pair(γ a, b)⁻¹ t_mi(γ) pair(a, b) ∈ Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- Scaling the Euclidean division by constants. -/
theorem k2PolyNagaoTorus_divmod_scale (α β : (ZMod p)ˣ) {a : Polynomial (ZMod p)} (ha : a ≠ 0)
    (b : Polynomial (ZMod p)) :
    (Polynomial.C (β : ZMod p) * b) / (Polynomial.C (α : ZMod p) * a) =
        Polynomial.C ((β * α⁻¹ : (ZMod p)ˣ) : ZMod p) * (b / a) ∧
      (Polynomial.C (β : ZMod p) * b) % (Polynomial.C (α : ZMod p) * a) =
        Polynomial.C (β : ZMod p) * (b % a) := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  have hu : Polynomial.C (α : ZMod p) * Polynomial.C ((β * α⁻¹ : (ZMod p)ˣ) : ZMod p) =
      Polynomial.C (β : ZMod p) := by
    rw [← map_mul (Polynomial.C : ZMod p →+* Polynomial (ZMod p)), ← Units.val_mul,
      mul_comm β α⁻¹, mul_inv_cancel_left]
  have ha' : Polynomial.C (α : ZMod p) * a ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.2 α.ne_zero) ha
  refine k2PolyNagaoWeyl_divmod_unique ha'
    (by linear_combination (-Polynomial.C (β : ZMod p)) * h1 - a * (b / a) * hu) ?_
  rw [Polynomial.degree_C_mul β.ne_zero, Polynomial.degree_C_mul α.ne_zero]
  exact Polynomial.degree_mod_lt b ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_divmod_scale

variable {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i) (hLi : L ≠ i)

/-- `t_mi(c)` lies in `S_K` when `m, i ∈ K`. -/
theorem k2PolyNagaoTorus_tmi_mem_S {K : Finset I} (hmK : m ∈ K) (hiK : i ∈ K)
    (c : (ZMod p)ˣ) : k2PolyDeg_torus p m i L hmi hmL hLi.symm c ∈ k2PolyDeg_S p K := by
  rw [k2PolyDeg_torus_apply]
  show w m i hmi (Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom c) *
      w m i hmi (-1 : (Polynomial (ZMod p))ˣ) ∈
    rootSpan (R := Polynomial (ZMod p)) fun a b => a ∈ K ∧ b ∈ K
  exact Subgroup.mul_mem _ (k2PolyDeg_w_mem_rootSpan m i hmi _ ⟨hmK, hiK⟩ ⟨hiK, hmK⟩)
    (k2PolyDeg_w_mem_rootSpan m i hmi _ ⟨hmK, hiK⟩ ⟨hiK, hmK⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_tmi_mem_S

/-- **Torus equivariance of the Euclidean word.**  For coprime `(a, b)`,
`pair(α a, β b)⁻¹ T(α, β) pair(a, b) ∈ Q`. -/
theorem k2PolyNagaoTorus_pair_mem {K : Finset I} (hmK : m ∈ K) (hiK : i ∈ K)
    (a : Polynomial (ZMod p)) :
    ∀ (α β : (ZMod p)ˣ) (b : Polynomial (ZMod p)), IsCoprime a b →
      (k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (α : ZMod p) * a)
          (Polynomial.C (β : ZMod p) * b))⁻¹ * k2PolyNagaoTorus_T p hmL hmi hLi α β *
        k2PolyNagaoSigma_pair p m L hmL a b ∈ k2PolyNF_Q p K L := by
  induction a using (Polynomial.degree_lt_wf (R := ZMod p)).induction with
  | _ a ih =>
    intro α β b hab
    by_cases ha : a = 0
    · subst ha
      obtain ⟨β₀, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit (isCoprime_zero_left.1 hab)
      have e : ∀ A B M : SteinbergGroup I (Polynomial (ZMod p)),
          ((A * B)⁻¹)⁻¹ * (B⁻¹ * M) * A⁻¹ = A * M * A⁻¹ := by
        intro A B M
        group
      rw [mul_zero (Polynomial.C (α : ZMod p)), k2PolyNagaoSigma_pair_zero,
        k2PolyNagaoSigma_pair_zero,
        ← map_mul (Polynomial.C : ZMod p →+* Polynomial (ZMod p)), ← Units.val_mul,
        mul_comm β β₀, k2PolyNagaoWeyl_tau_C hmL hmi hLi, k2PolyNagaoWeyl_tau_C hmL hmi hLi,
        k2PolyNagaoTorus_T, map_mul (k2PolyDeg_torus p m L i hmL hmi hLi) β₀ β, e]
      exact Subgroup.mem_sup_left (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L)
        (k2PolyDeg_torus_conj_rootSpan m L i hmL hmi hLi (fun a b => a ∈ K ∧ b ∈ K) β₀
          (k2PolyNagaoTorus_tmi_mem_S hmL hmi hLi hmK hiK (α * β)))
    · have hCa : Polynomial.C (α : ZMod p) * a ≠ 0 :=
        mul_ne_zero (Polynomial.C_ne_zero.2 α.ne_zero) ha
      obtain ⟨hq, hr⟩ := k2PolyNagaoTorus_divmod_scale α β ha b
      have hih := ih (b % a) (Polynomial.degree_mod_lt b ha) β α (-a)
        (k2PolyNagaoWeyl_coprime_step hab)
      have key : ∀ A X X' V P P' : SteinbergGroup I (Polynomial (ZMod p)), A * X = X' * A →
          (X' * V * P')⁻¹ * A * (X * V * P) = P'⁻¹ * (V⁻¹ * A * V) * P := by
        intro A X X' V P P' hA
        calc (X' * V * P')⁻¹ * A * (X * V * P) = P'⁻¹ * V⁻¹ * X'⁻¹ * (A * X) * V * P := by
              group
          _ = P'⁻¹ * (V⁻¹ * A * V) * P := by
              rw [hA]
              group
      rw [k2PolyNagaoSigma_pair_of_ne p m L hmL hCa, k2PolyNagaoSigma_pair_of_ne p m L hmL ha,
        hq, hr, ← mul_neg (Polynomial.C (α : ZMod p)) a,
        key _ _ _ _ _ _ (k2PolyNagaoTorus_T_mul_x hmL hmi hLi α β (b / a)),
        k2PolyNagaoTorus_W_conj_T hmL hmi hLi α β]
      exact hih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_pair_mem

/-- The case `β = 1`: `pair(γ a, b)⁻¹ t_mi(γ) pair(a, b) ∈ Q` for coprime `(a, b)`. -/
theorem k2PolyNagaoTorus_pair_mem_one {K : Finset I} (hmK : m ∈ K) (hiK : i ∈ K)
    (γ : (ZMod p)ˣ) {a b : Polynomial (ZMod p)} (hab : IsCoprime a b) :
    (k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (γ : ZMod p) * a) b)⁻¹ *
        k2PolyDeg_torus p m i L hmi hmL hLi.symm γ * k2PolyNagaoSigma_pair p m L hmL a b ∈
      k2PolyNF_Q p K L := by
  have h := k2PolyNagaoTorus_pair_mem hmL hmi hLi hmK hiK a γ 1 b hab
  simp only [k2PolyNagaoTorus_T, map_one, inv_one, one_mul, mul_one, Units.val_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_pair_mem_one

end GroupApproximation.BooneHigman.Metabelian.ElemFP
