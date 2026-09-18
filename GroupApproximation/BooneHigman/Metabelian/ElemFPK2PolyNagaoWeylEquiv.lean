import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 4: equivariance of the Euclidean word under the constant torus

Lane `bh-met-93d`.  Notation of `ElemFPK2PolyNagaoWeylTorus`; `pair = k2PolyNagaoSigma_pair`.

* `k2PolyNagaoWeyl_divmod_small`: `deg b < deg a` gives `b / a = 0` and `b % a = b`.
* `k2PolyNagaoWeyl_torus_mul_pair`: for a coprime column `(a, b)` and `δ ∈ F_pˣ`,
  `t(δ) · pair a b = pair (δ a) (δ⁻¹ b)`.  Proved by well-founded induction on `deg a`
  (`Polynomial.degree_lt_wf`), following the recursion that defines `pair`:
  - `a = 0`: `b = C β` is a unit and `τ(C β) = t(β)⁻¹`, the torus being a homomorphism;
  - `a ≠ 0`: `(δ⁻¹ b) / (δ a) = δ⁻² (b / a)`, `(δ⁻¹ b) % (δ a) = δ⁻¹ (b % a)`,
    `t(δ) x'(f) = x'(δ⁻² f) t(δ)` and `W⁻¹ t(δ) W = t(δ⁻¹)`, then the induction hypothesis
    at `(b % a, -a)` and `δ⁻¹`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `deg b < deg a` gives `b / a = 0` and `b % a = b`. -/
theorem k2PolyNagaoWeyl_divmod_small {a b : Polynomial (ZMod p)} (ha : a ≠ 0)
    (h : b.degree < a.degree) : b / a = 0 ∧ b % a = b :=
  k2PolyNagaoWeyl_divmod_unique ha (by ring) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_divmod_small

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

/-- **Torus equivariance.**  `t(δ) · pair a b = pair (δ a) (δ⁻¹ b)` for coprime `(a, b)`. -/
theorem k2PolyNagaoWeyl_torus_mul_pair (a : Polynomial (ZMod p)) :
    ∀ (δ : (ZMod p)ˣ) (b : Polynomial (ZMod p)), IsCoprime a b →
      k2PolyDeg_torus p m L n hmL hmn hLn δ * k2PolyNagaoSigma_pair p m L hmL a b =
        k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (δ : ZMod p) * a)
          (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * b) := by
  induction a using (Polynomial.degree_lt_wf (R := ZMod p)).induction with
  | _ a ih =>
    intro δ b hab
    by_cases ha : a = 0
    · subst ha
      obtain ⟨β, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit (isCoprime_zero_left.1 hab)
      rw [mul_zero (Polynomial.C (δ : ZMod p)), k2PolyNagaoSigma_pair_zero,
        k2PolyNagaoSigma_pair_zero, ← map_mul Polynomial.C, ← Units.val_mul,
        k2PolyNagaoWeyl_tau_C hmL hmn hLn, k2PolyNagaoWeyl_tau_C hmL hmn hLn, mul_comm δ⁻¹ β,
        map_mul, map_inv, mul_inv_rev, inv_inv]
    · have hCa : Polynomial.C (δ : ZMod p) * a ≠ 0 :=
        mul_ne_zero (Polynomial.C_ne_zero.2 δ.ne_zero) ha
      obtain ⟨hq, hr⟩ := k2PolyNagaoWeyl_divmod_scale δ ha b
      have hih := ih (b % a) (Polynomial.degree_mod_lt b ha) δ⁻¹ (-a)
        (k2PolyNagaoWeyl_coprime_step hab)
      have key : ∀ T X X' V P : SteinbergGroup I (Polynomial (ZMod p)), T * X = X' * T →
          T * (X * V * P) = X' * V * (V⁻¹ * T * V * P) := by
        intro T X X' V P hTX
        calc T * (X * V * P) = T * X * V * P := by group
          _ = X' * T * V * P := by rw [hTX]
          _ = X' * V * (V⁻¹ * T * V * P) := by group
      rw [k2PolyNagaoSigma_pair_of_ne p m L hmL ha, k2PolyNagaoSigma_pair_of_ne p m L hmL hCa,
        hq, hr, key _ _ _ _ _ (k2PolyNagaoWeyl_torus_mul_x hmL hmn hLn δ (b / a)),
        k2PolyNagaoWeyl_W_conj_torus hmL hmn hLn δ, hih, inv_inv, mul_neg,
        mul_right_comm (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p)) (b / a)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_torus_mul_pair

end GroupApproximation.BooneHigman.Metabelian.ElemFP
