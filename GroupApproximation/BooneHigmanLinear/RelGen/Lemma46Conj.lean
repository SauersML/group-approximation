import GroupApproximation.BooneHigmanLinear.RelGen.Lemma46
import GroupApproximation.Meta.AxiomGuard

/-!
# L–S Lemma 4.6 (1)–(3), conjugation form (k2-poly H.L3)

Lane k2-hl3b. Corollaries of `RelGen.Lemma46` in the conjugation form of `LSCore.ZC46`:
`c_β(s, t)^{x_α(η)} = x_α(η)⁻¹ · c_β(s, t) · x_α(η)`. The statements match the `LSCore` ones
verbatim with `cj g y` written out as `g⁻¹ * y * g`, so `LSCore.ZC46` can bridge by `exact`.

From `⁅c, x_α(-η)⁆ = a · b` (Lemma 46, with `ξ = -η`) we get
`x_α(η)⁻¹ c x_α(η) = b⁻¹ a⁻¹ c` (`conj_inv_of_comm`).
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

theorem conj_inv_of_comm {G : Type*} [Group G] {c g y a b : G} (h : ⁅c, y⁆ = a * b)
    (hy : y = g⁻¹) : g⁻¹ * c * g = b⁻¹ * a⁻¹ * c := by
  subst hy
  have e : g⁻¹ * c * g = ⁅c, g⁻¹⁆⁻¹ * c := by
    rw [commutatorElement_def]
    group
  rw [e, h, mul_inv_rev]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_inv_of_comm

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- **L–S 4.6(3)**, conjugation form (`LSCore.c_conj_disj`). -/
theorem cElt_conj_disj {p q k l : I} (hpq : p ≠ q) (hkl : k ≠ l) (hkp : k ≠ p) (hkq : k ≠ q)
    (hlp : l ≠ p) (hlq : l ≠ q) (s t η : R) :
    (x k l hkl η)⁻¹ * cElt p q hpq s t * x k l hkl η = cElt p q hpq s t := by
  have h := commutatorElement_eq_one_iff_mul_comm.mp
    (comm_cElt_x_disj hpq hkl hkp hkq hlp hlq s t η)
  rw [mul_assoc, h, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_disj

/-- **L–S 4.6(1)**, `α = (i, j)`, `β = (j, l)` (`LSCore.c_conj_obtuse_row`). -/
theorem cElt_conj_obtuse_row {i j l : I} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t η : R) :
    (x i j hij η)⁻¹ * cElt j l hjl s t * x i j hij η =
      x i l hil (s ^ 2 * t * η) * x i j hij (-(s * t * η)) * cElt j l hjl s t := by
  rw [conj_inv_of_comm (comm_cElt_x_ki hjl hij hil s t (-η)) (x_neg i j hij η), ← x_neg,
    ← x_neg]
  congr 1
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_obtuse_row

/-- **L–S 4.6(1)**, `α = (i, j)`, `β = (k, i)` (`LSCore.c_conj_obtuse_col`). -/
theorem cElt_conj_obtuse_col {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s t η : R) :
    (x i j hij η)⁻¹ * cElt k i hki s t * x i j hij η =
      x k j hkj (-(s ^ 2 * t * η)) * x i j hij (-(s * t * η)) * cElt k i hki s t := by
  rw [conj_inv_of_comm (comm_cElt_x_jl hki hkj hij s t (-η)) (x_neg i j hij η), ← x_neg,
    ← x_neg]
  congr 1
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_obtuse_col

/-- **L–S 4.6(2)**, `α = (i, j)`, `β = (i, l)` (`LSCore.c_conj_acute_row`). -/
theorem cElt_conj_acute_row {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (s t η : R) :
    (x i j hij η)⁻¹ * cElt i l hil s t * x i j hij η =
      x i j hij (s * t * η + s ^ 2 * t ^ 2 * η) * x l j hlj (s * t ^ 2 * η) *
        cElt i l hil s t := by
  rw [conj_inv_of_comm (comm_cElt_x_il hil hij hlj s t (-η)) (x_neg i j hij η), ← x_neg,
    ← x_neg]
  congr 1
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_acute_row

/-- **L–S 4.6(2)**, `α = (i, j)`, `β = (k, j)` (`LSCore.c_conj_acute_col`). -/
theorem cElt_conj_acute_col {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (s t η : R) :
    (x i j hij η)⁻¹ * cElt k j hkj s t * x i j hij η =
      x i j hij (s * t * η + s ^ 2 * t ^ 2 * η) * x i k hik (-(s * t ^ 2 * η)) *
        cElt k j hkj s t := by
  rw [conj_inv_of_comm (comm_cElt_x_kj hkj hik hij s t (-η)) (x_neg i j hij η), ← x_neg,
    ← x_neg]
  congr 1
  exact x_mul_x_congr (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_acute_col

end GroupApproximation.BooneHigmanLinear.RelGen
