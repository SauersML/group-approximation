import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoSigmaDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao normal forms for `K₂(F_p[X])`, part 5: the checks of `σ` that are proved outright

Lane `bh-met-92q`.  For the Euclidean section `σ = k2PolyNagaoSigma_sigma` of
`ElemFPK2PolyNagaoSigmaDef`:

* `k2PolyNagaoSigma_check_Lm`: the coset check of **every** `x_Lm(f)`, `f ∈ F_p[X]`.  If
  `v m ≠ 0`, the Euclidean words of `v` and `x_Lm(f) v` differ only in their first letter
  (`(b + f a) / a = b / a + f`, `(b + f a) % a = b % a`), so the check element is `1`.  If
  `v m = 0`, it is `τ(v L)⁻¹ x_Lm(f) τ(v L)`, a root `x_Lm(c)` (`k2PolyDeg_h_conj_exists`).
* `k2PolyNagaoSigma_check_W_lt`: the coset check of `W' = w_mL(-1)` at the vectors with
  `deg v m < deg v L`: there `σ(W' v) = W' σ(v)`, so the check element is `1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (x_mem_rootSpan act
  act_mul act_x_apply)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- `W' = w_mL(-1)` acts on the `(m, L)` coordinates by `(c, d) ↦ (-d, c)`. -/
theorem k2PolyNagaoSigma_act_W {R : Type*} [CommRing R] {m L : I} (hmL : m ≠ L)
    (v : I → R) :
    act (w m L hmL (-1 : Rˣ)) v m = -(v L) ∧ act (w m L hmL (-1 : Rˣ)) v L = v m := by
  have hA : ∀ (a : R) (z : I → R), act (x m L hmL a) z m = z m + a * z L := fun a z => by
    rw [act_x_apply, if_pos rfl]
  have hA' : ∀ (a : R) (z : I → R), act (x m L hmL a) z L = z L := fun a z => by
    rw [act_x_apply, if_neg hmL.symm, add_zero]
  have hB : ∀ (a : R) (z : I → R), act (x L m hmL.symm a) z L = z L + a * z m :=
    fun a z => by rw [act_x_apply, if_pos rfl]
  have hB' : ∀ (a : R) (z : I → R), act (x L m hmL.symm a) z m = z m := fun a z => by
    rw [act_x_apply, if_neg hmL, add_zero]
  have hu : ((-1 : Rˣ) : R) = -1 := by rw [Units.val_neg, Units.val_one]
  have hui : (((-1 : Rˣ)⁻¹ : Rˣ) : R) = -1 := by
    rw [inv_neg, inv_one, Units.val_neg, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [w, act_mul, act_mul, hA, hB', hB, hA, hA', hu, hui]
    ring
  · rw [w, act_mul, act_mul, hA', hB, hA', hA, hu, hui]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_act_W

variable {p : ℕ} [Fact p.Prime]

/-- `(b + f a) % a = b % a`. -/
theorem k2PolyNagaoSigma_mod_add (a b f : Polynomial (ZMod p)) :
    (b + f * a) % a = b % a := by
  have hz : f * a % a = 0 := EuclideanDomain.mod_eq_zero.2 (dvd_mul_left a f)
  rw [Polynomial.add_mod, hz, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_mod_add

/-- `(b + f a) / a = b / a + f` for `a ≠ 0`. -/
theorem k2PolyNagaoSigma_div_add {a : Polynomial (ZMod p)} (ha : a ≠ 0)
    (b f : Polynomial (ZMod p)) : (b + f * a) / a = b / a + f := by
  have h1 : a * ((b + f * a) / a) + b % a = b + f * a := by
    rw [← k2PolyNagaoSigma_mod_add a b f]
    exact EuclideanDomain.div_add_mod _ _
  have h2 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod _ _
  apply mul_left_cancel₀ ha
  linear_combination h1 - h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_div_add

/-- Every `x_Lm(c)` (`m ∈ K`) lies in `Q = S ⊔ V`. -/
theorem k2PolyNagaoSigma_x_mem_Q {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (c : Polynomial (ZMod p)) : x L m hmL.symm c ∈ k2PolyNF_Q p K L := by
  unfold k2PolyNF_Q
  exact Subgroup.mem_sup_right (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hmL.symm c
    ⟨rfl, hmK⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_x_mem_Q

/-- `τ(b)⁻¹ x_Lm(f) τ(b) ∈ Q`. -/
theorem k2PolyNagaoSigma_tau_conj {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∃ n, m ≠ n ∧ L ≠ n) (b f : Polynomial (ZMod p)) :
    (k2PolyNagaoSigma_tau p m L hmL b)⁻¹ * x L m hmL.symm f * k2PolyNagaoSigma_tau p m L hmL b
      ∈ k2PolyNF_Q p K L := by
  by_cases hb1 : b = 1
  · rw [k2PolyNagaoSigma_tau, if_pos hb1, inv_one, one_mul, mul_one]
    exact k2PolyNagaoSigma_x_mem_Q hmL hmK f
  by_cases hbu : IsUnit b
  · rw [k2PolyNagaoSigma_tau, if_neg hb1, dif_pos hbu, inv_inv]
    obtain ⟨c, hc⟩ := k2PolyDeg_h_conj_exists m L L m hmL hmL.symm hthird hbu.unit f
    rw [hc]
    exact k2PolyNagaoSigma_x_mem_Q hmL hmK c
  · rw [k2PolyNagaoSigma_tau, if_neg hb1, dif_neg hbu, inv_one, one_mul, mul_one]
    exact k2PolyNagaoSigma_x_mem_Q hmL hmK f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_tau_conj
