import GroupApproximation.BooneHigmanLinear.LSCore.ZC5
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The conjugation identities behind Lavrenov–Sinchuk Lemma 5.22 (k2-poly H.L4)

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25
(2020), arXiv:1909.02637, proof of Lemma 5.22. Lane k2-hl4c.

L–S conjugate each generator of `K(α, β)` (Def 5.16) by `x_α(aX⁻¹)` inside
`St(Φ, A[X, X⁻¹])`. This file proves those identities in type `A_I` over any commutative ring
`R` with elements `t, t'` and `t t' = 1` (`t = X`, `t' = X⁻¹`), so it needs no Laurent-polynomial
API. With `α = (i, j)` and conjugation `y^g = g⁻¹ y g` (`cj g y`), the cases are:
* K1, `z_γ(Xf, ξ)` with `α + γ ∈ Φ`, i.e. L–S (5.9): `conjK1_obtuse_row` for `γ = (j, l)` and
  `conjK1_obtuse_col` for `γ = (l, i)`;
* K1 with `α - γ ∈ Φ`, i.e. L–S (5.10): `conjK1_acute_row` for `γ = (i, l)` and
  `conjK1_acute_col` for `γ = (l, j)`;
* K2, `x_{-β}(X²f)` with `β = (i, k)` (`conjK2_negBeta`), and `x_{-α}(X²f)` through Lemma 4.1(5)
  with the auxiliary root `δ = (i, d)` (`conjK2_negAlpha`);
* K4, `x_{β-α}(Xf)` (`conjK4_betaSubAlpha`). The remaining K3/K4 generators and `x_α` commute
  with `x_α(aX⁻¹)` (`cj_x_self`, and `cj_of_commute` with `x_commute_of_ne`).

`zElt_neg_eq_cElt` is L–S (4.2) in the form used at the end of the proof of 5.22:
`z_δ(s, -u) = x_δ(s) · c_δ(-s, u)`. The membership bookkeeping (which factor is a generator of
which type) is done in `LSCore/Conj.lean` against the generator sets of `LSCore/KDecomp.lean`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt cElt)

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- `x_ij` commutes with itself. -/
theorem cj_x_self {i j : I} (hij : i ≠ j) (a c : R) :
    cj (x i j hij a) (x i j hij c) = x i j hij c := by
  refine cj_of_commute ?_
  rw [commute_iff_eq, x_mul, x_mul, add_comm]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.cj_x_self

/-- **L–S (4.2)**, rearranged: `z_pq(s, -u) = x_pq(s) · c_pq(-s, u)`. -/
theorem zElt_neg_eq_cElt {p q : I} (hpq : p ≠ q) (s u : R) :
    zElt p q hpq s (-u) = x p q hpq s * cElt p q hpq (-s) u := by
  unfold zElt cElt
  rw [commutatorElement_def]
  simp only [neg_neg, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.zElt_neg_eq_cElt

section Laurent

variable {t t' : R} (ht : t * t' = 1)
include ht

/-- **L–S (5.9)**, `γ = (j, l)`: `z_γ(Xf, ξ)^{x_α(aX⁻¹)} = x_α(-afξ) · x_{α+γ}(-af) · z_γ(Xf, ξ)`. -/
theorem conjK1_obtuse_row {i j l : I} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a f ξ : R) :
    cj (x i j hij (a * t')) (zElt j l hjl (t * f) ξ) =
      x i j hij (-(a * f * ξ)) * x i l hil (-(a * f)) * zElt j l hjl (t * f) ξ := by
  have h1 : t * f * ξ * (a * t') = a * f * ξ := by linear_combination (a * f * ξ) * ht
  have h2 : t * f * (a * t') = a * f := by linear_combination (a * f) * ht
  rw [z_conj_obtuse_row hij hjl hil, h1, h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK1_obtuse_row

/-- **L–S (5.9)**, `γ = (l, i)`: `z_γ(Xf, ξ)^{x_α(aX⁻¹)} = x_α(-afξ) · x_{γ+α}(af) · z_γ(Xf, ξ)`. -/
theorem conjK1_obtuse_col {i j l : I} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (a f ξ : R) :
    cj (x i j hij (a * t')) (zElt l i hli (t * f) ξ) =
      x i j hij (-(a * f * ξ)) * x l j hlj (a * f) * zElt l i hli (t * f) ξ := by
  have h1 : t * f * ξ * (a * t') = a * f * ξ := by linear_combination (a * f * ξ) * ht
  have h2 : t * f * (a * t') = a * f := by linear_combination (a * f) * ht
  rw [z_conj_obtuse_col hij hli hlj, h1, h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK1_obtuse_col

/-- **L–S (5.10)**, `γ = (i, l)`:
`z_γ(Xf, ξ)^{x_α(aX⁻¹)} = x_α(afξ) · x_{α-γ}(-afξ²) · z_γ(Xf, ξ)`. -/
theorem conjK1_acute_row {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (a f ξ : R) :
    cj (x i j hij (a * t')) (zElt i l hil (t * f) ξ) =
      x i j hij (a * f * ξ) * x l j hlj (-(a * f * ξ ^ 2)) * zElt i l hil (t * f) ξ := by
  have h1 : t * f * ξ * (a * t') = a * f * ξ := by linear_combination (a * f * ξ) * ht
  have h2 : t * f * ξ ^ 2 * (a * t') = a * f * ξ ^ 2 := by
    linear_combination (a * f * ξ ^ 2) * ht
  rw [z_conj_acute_row hij hil hlj, h1, h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK1_acute_row

/-- **L–S (5.10)**, `γ = (l, j)`:
`z_γ(Xf, ξ)^{x_α(aX⁻¹)} = x_α(afξ) · x_{α-γ}(afξ²) · z_γ(Xf, ξ)`. -/
theorem conjK1_acute_col {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (a f ξ : R) :
    cj (x i j hij (a * t')) (zElt l j hlj (t * f) ξ) =
      x i j hij (a * f * ξ) * x i l hil (a * f * ξ ^ 2) * zElt l j hlj (t * f) ξ := by
  have h1 : t * f * ξ * (a * t') = a * f * ξ := by linear_combination (a * f * ξ) * ht
  have h2 : t * f * ξ ^ 2 * (a * t') = a * f * ξ ^ 2 := by
    linear_combination (a * f * ξ ^ 2) * ht
  rw [z_conj_acute_col hij hil hlj, h1, h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK1_acute_col

/-- L–S 5.22, generator `x_{-β}(X²f)` with `β = (i, k)`, by (R2):
`x_{-β}(X²f)^{x_α(aX⁻¹)} = x_{α-β}(aXf) · x_{-β}(X²f)`. -/
theorem conjK2_negBeta {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a f : R) :
    cj (x i j hij (a * t')) (x k i hki (t ^ 2 * f)) =
      x k j hkj (a * (t * f)) * x k i hki (t ^ 2 * f) := by
  have h1 : t ^ 2 * f * (a * t') = a * (t * f) := by linear_combination (a * t * f) * ht
  rw [cj_x_left hki hij hkj, h1]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK2_negBeta

/-- L–S 5.22, generator `x_{β-α}(Xf)` with `β - α = (j, k)`, by (R2):
`x_{β-α}(Xf)^{x_α(aX⁻¹)} = x_β(-af) · x_{β-α}(Xf)`. -/
theorem conjK4_betaSubAlpha {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a f : R) :
    cj (x i j hij (a * t')) (x j k hjk (t * f)) = x i k hik (-(a * f)) * x j k hjk (t * f) := by
  have h1 : a * t' * (t * f) = a * f := by linear_combination (a * f) * ht
  rw [cj_x_right hij hjk hik, h1]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK4_betaSubAlpha

/-- L–S 5.22, the generator `x_{-α}(X²f)`, through Lemma 4.1(5) with the auxiliary root
`δ = (i, d)` (acute with `α`, so `δ - α = (j, d)` and `α - δ = (d, j)` are roots). This is
L–S's display at the end of the proof of 5.22:
`z_{-α}(X²f, aX⁻¹) = x_{δ-α}(Xf) x_δ(-af) x_{-δ}(aX²f) x_{-α}(X²f) z_{δ-α}(-Xf, -a)
x_{α-δ}(-a²Xf) x_α(-a²f) z_δ(af, -X)`. -/
theorem conjK2_negAlpha {i j d : I} (hij : i ≠ j) (hjd : j ≠ d) (hdi : d ≠ i) (a f : R) :
    cj (x i j hij (a * t')) (x j i hij.symm (t ^ 2 * f)) =
      x j d hjd (t * f) * x i d hdi.symm (-(a * f)) * x d i hdi (a * f * t ^ 2) *
        x j i hij.symm (t ^ 2 * f) * zElt j d hjd (-(t * f)) (-a) *
        x d j hjd.symm (-(a ^ 2 * (t * f))) * x i j hij (-(a ^ 2 * f)) *
        zElt i d hdi.symm (a * f) (-t) := by
  have h0 : cj (x i j hij (a * t')) (x j i hij.symm (t ^ 2 * f)) =
      zElt j i hij.symm (t * f * t) (a * t') := by
    rw [show t * f * t = t ^ 2 * f by ring]
    exact (zElt_eq_cj hij.symm _ _).symm
  have h1 : t * f * (a * t') = a * f := by linear_combination (a * f) * ht
  have h2 : t * f * t = t ^ 2 * f := by ring
  have h3 : a * t' * t = a := by linear_combination a * ht
  have h4 : t * f * (a * t') ^ 2 * t ^ 2 = a ^ 2 * (t * f) := by
    linear_combination (a ^ 2 * t * f * (t * t' + 1)) * ht
  have h5 : t * f * (a * t') ^ 2 * t = a ^ 2 * f := by
    linear_combination (a ^ 2 * f * (t * t' + 1)) * ht
  rw [h0, z_add_eq hjd hdi hij.symm, h1, h2, h3, h4, h5]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.conjK2_negAlpha

end Laurent

end LSCore
end BooneHigmanLinear
end GroupApproximation
