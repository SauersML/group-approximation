import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylLt
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 6: the two tails of the case `deg b = deg a`

Lane `bh-met-93d`.  Notation of `ElemFPK2PolyNagaoWeylLt`.  In the case `deg b = deg a` of the
Weyl check (`ElemFPK2PolyNagaoWeylEq`), with `b = γ a + r`, `deg r < deg a`, `γ ∈ F_pˣ` and
`δ = -γ⁻¹`, the check element reduces to `(pair (δ r) b)⁻¹ · t(δ) · x'(δ) · pair r (-a)`.

* `k2PolyNagaoWeyl_eq_tail_ne` (`r ≠ 0`): `x'(δ) · pair r (-a) = pair r (-a + δ r)` (only the
  first quotient moves), then torus equivariance gives `t(δ) pair r (-a + δ r) = pair (δ r) b`,
  so the element is `1`.
* `k2PolyNagaoWeyl_eq_tail_zero` (`r = 0`, `a = C α`, `b = C γ C α`): the element is
  `t(γα) t(δ) x'(δ) t(γαδ)⁻¹`, a torus conjugate of a root `x'(·)`, hence in `Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

/-- **Tail, `r ≠ 0`.** -/
theorem k2PolyNagaoWeyl_eq_tail_ne {a b r : Polynomial (ZMod p)} (γ δ : (ZMod p)ˣ)
    (hab : IsCoprime a b) (hr0 : r ≠ 0) (hr_def : r = b - Polynomial.C (γ : ZMod p) * a)
    (hδγ : Polynomial.C (δ : ZMod p) * Polynomial.C (γ : ZMod p) = -1)
    (hδinv : Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) = -Polynomial.C (γ : ZMod p)) :
    (k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (δ : ZMod p) * r) b)⁻¹ *
      (k2PolyDeg_torus p m L n hmL hmn hLn δ * x L m hmL.symm (Polynomial.C (δ : ZMod p)) *
        k2PolyNagaoSigma_pair p m L hmL r (-a)) = 1 := by
  have hδδ : Polynomial.C (δ : ZMod p) * Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← map_mul Polynomial.C, Units.mul_inv, map_one]
  have hshift : x L m hmL.symm (Polynomial.C (δ : ZMod p)) *
      k2PolyNagaoSigma_pair p m L hmL r (-a) =
      k2PolyNagaoSigma_pair p m L hmL r (-a + Polynomial.C (δ : ZMod p) * r) := by
    rw [k2PolyNagaoSigma_pair_of_ne p m L hmL hr0, k2PolyNagaoSigma_pair_of_ne p m L hmL hr0,
      k2PolyNagaoSigma_mod_add, k2PolyNagaoSigma_div_add hr0, add_comm (-a / r), ← x_mul]
    simp only [mul_assoc]
  have hcop2 : IsCoprime r (-a + Polynomial.C (δ : ZMod p) * r) :=
    k2PolyNagaoWeyl_isCoprime_of_comb hab (x1 := Polynomial.C (δ : ZMod p)) (y1 := -1)
      (x2 := 0) (y2 := -Polynomial.C (γ : ZMod p)) (by ring)
      (by linear_combination -hr_def + r * hδγ)
  have hb' : Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) *
      (-a + Polynomial.C (δ : ZMod p) * r) = b := by
    linear_combination -a * hδinv + r * hδδ + hr_def
  rw [mul_assoc (k2PolyDeg_torus p m L n hmL hmn hLn δ), hshift,
    k2PolyNagaoWeyl_torus_mul_pair hmL hmn hLn r δ _ hcop2, hb', inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_eq_tail_ne

/-- **Tail, `r = 0`.**  Here `a = C α`, `b = C γ · C α` and `γ α δ = -α`. -/
theorem k2PolyNagaoWeyl_eq_tail_zero {K : Finset I} (hmK : m ∈ K) (α γ δ : (ZMod p)ˣ)
    (hu : γ * α * δ = -α) :
    (k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (δ : ZMod p) * 0)
        (Polynomial.C (γ : ZMod p) * Polynomial.C (α : ZMod p)))⁻¹ *
      (k2PolyDeg_torus p m L n hmL hmn hLn δ * x L m hmL.symm (Polynomial.C (δ : ZMod p)) *
        k2PolyNagaoSigma_pair p m L hmL 0 (-Polynomial.C (α : ZMod p))) ∈ k2PolyNF_Q p K L := by
  have hn : -Polynomial.C (α : ZMod p) = Polynomial.C ((-α : (ZMod p)ˣ) : ZMod p) := by
    rw [Units.val_neg, map_neg]
  have e : ∀ A X T : SteinbergGroup I (Polynomial (ZMod p)),
      A * (X * T * (A * T)⁻¹) = A * X * A⁻¹ := fun A X T => by group
  rw [mul_zero (Polynomial.C (δ : ZMod p)), k2PolyNagaoSigma_pair_zero,
    k2PolyNagaoSigma_pair_zero, ← map_mul Polynomial.C, ← Units.val_mul, hn,
    k2PolyNagaoWeyl_tau_C hmL hmn hLn, k2PolyNagaoWeyl_tau_C hmL hmn hLn, inv_inv, ← hu,
    map_mul (k2PolyDeg_torus p m L n hmL hmn hLn) (γ * α) δ,
    k2PolyNagaoWeyl_torus_mul_x hmL hmn hLn δ, e,
    k2PolyNagaoWeyl_torus_mul_x hmL hmn hLn (γ * α), mul_inv_cancel_right]
  exact k2PolyNagaoSigma_x_mem_Q hmL hmK _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_eq_tail_zero

end GroupApproximation.BooneHigman.Metabelian.ElemFP
