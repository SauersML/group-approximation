import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyEuclidGen
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao-style normal forms for `K₂(F_p[X])`, part 1: a root family is good on monomials

Lane `bh-met-92k`.  Notation of `ElemFPK2PolyEuclidGen`: `R = F_p[X]`, `G = G_{K ∪ {L}}(R)`,
`Q = S_K ⊔ V`, and `g ∈ G` is *good* for a set map `σ` (`k2PolyEuclid_Good`) when
`σ(g v)⁻¹ g σ(v) ∈ Q` on the whole orbit `G e_L`.

* `k2PolyNagao_good_one`: `1` is good.
* `k2PolyNagao_good_x_add`, `k2PolyNagao_good_x_neg`, `k2PolyNagao_good_x_nsmul`: the
  coefficients `a` with `x_ij(a)` good form an additive submonoid closed under negation
  (`x_ij(a + b) = x_ij(a) x_ij(b)`, `x_ij(-a) = x_ij(a)⁻¹`).
* `k2PolyNagao_good_x_of_pow`: if `x_ij(X^k)` is good for every `k : ℕ`, then `x_ij(f)` is
  good for every `f ∈ F_p[X]`.  A monomial is `c X^k = c.val • X^k`, and a polynomial is a
  sum of monomials (`Polynomial.induction_on'`).

Truth check: matrix shadow of the monomial decomposition, scratchpad `bh-met-92k/chk.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act_one)

variable {I : Type} [Fintype I] [DecidableEq I]
variable {p : ℕ} [Fact p.Prime]

/-- The identity is good. -/
theorem k2PolyNagao_good_one {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} :
    k2PolyEuclid_Good p K L σ 1 := by
  refine ⟨Subgroup.one_mem _, fun v _ => ?_⟩
  rw [act_one, mul_one, inv_mul_cancel]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_one

/-- `x_ij(a + b) = x_ij(a) x_ij(b)` is good when `x_ij(a)` and `x_ij(b)` are. -/
theorem k2PolyNagao_good_x_add {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} {i j : I}
    (hij : i ≠ j) {a b : Polynomial (ZMod p)} (ha : k2PolyEuclid_Good p K L σ (x i j hij a))
    (hb : k2PolyEuclid_Good p K L σ (x i j hij b)) :
    k2PolyEuclid_Good p K L σ (x i j hij (a + b)) := by
  rw [← x_mul]
  exact k2PolyEuclid_good_mul ha hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_x_add

/-- `x_ij(-a) = x_ij(a)⁻¹` is good when `x_ij(a)` is. -/
theorem k2PolyNagao_good_x_neg {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} {i j : I}
    (hij : i ≠ j) {a : Polynomial (ZMod p)} (ha : k2PolyEuclid_Good p K L σ (x i j hij a)) :
    k2PolyEuclid_Good p K L σ (x i j hij (-a)) := by
  rw [x_neg]
  exact k2PolyEuclid_good_inv ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_x_neg

/-- `x_ij(k • a) = x_ij(a)^k` is good when `x_ij(a)` is. -/
theorem k2PolyNagao_good_x_nsmul {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} {i j : I}
    (hij : i ≠ j) {a : Polynomial (ZMod p)} (ha : k2PolyEuclid_Good p K L σ (x i j hij a))
    (k : ℕ) : k2PolyEuclid_Good p K L σ (x i j hij (k • a)) := by
  induction k with
  | zero =>
    rw [zero_nsmul, x_zero]
    exact k2PolyNagao_good_one
  | succ k ih =>
    rw [succ_nsmul]
    exact k2PolyNagao_good_x_add hij ih ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_x_nsmul

omit [Fact p.Prime] in
/-- A monomial over `F_p` is a natural multiple of a power of `X`. -/
theorem k2PolyNagao_monomial_eq [NeZero p] (k : ℕ) (c : ZMod p) :
    Polynomial.monomial k c = c.val • (Polynomial.X ^ k : Polynomial (ZMod p)) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, nsmul_eq_mul, ← Polynomial.C_eq_natCast,
    ZMod.natCast_zmod_val]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_monomial_eq

/-- **Monomial reduction.**  If `x_ij(X^k)` is good for every `k`, then `x_ij(f)` is good for
every `f ∈ F_p[X]`. -/
theorem k2PolyNagao_good_x_of_pow {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} {i j : I}
    (hij : i ≠ j)
    (hpow : ∀ k : ℕ, k2PolyEuclid_Good p K L σ (x i j hij (Polynomial.X ^ k)))
    (f : Polynomial (ZMod p)) : k2PolyEuclid_Good p K L σ (x i j hij f) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine Polynomial.induction_on' f (fun f g hf hg => k2PolyNagao_good_x_add hij hf hg)
    (fun k c => ?_)
  rw [k2PolyNagao_monomial_eq k c]
  exact k2PolyNagao_good_x_nsmul hij (hpow k) c.val

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_x_of_pow

end GroupApproximation.BooneHigman.Metabelian.ElemFP
