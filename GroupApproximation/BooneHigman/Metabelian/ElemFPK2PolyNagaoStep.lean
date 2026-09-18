import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoMono
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao-style normal forms for `K₂(F_p[X])`, part 2: the degree step

Lane `bh-met-92k`.  Fix `m ∈ K`, `m ≠ L`, a third index `n ∉ {m, L}`, and (for the degree
step) a second index `i ∈ K`, `i ≠ m`.  Assume the constant roots `x_im(1)`, `x_mi(1)`,
`x_mL(1)`, `x_Lm(1)` are good.  Per coefficient `f` (unlike `ElemFPK2PolyEuclidRoots`, whose
lemmas assume all of the family `x_Lm(·)`):

* `x_mL(f) = W x_Lm(-f) W⁻¹` with `W = x_mL(1) x_Lm(-1) x_mL(1)` (`k2PolyNagao_good_mL`);
* `x_iL(f) = ⁅x_im(1), x_mL(f)⁆`, `x_im(f) = ⁅x_iL(f), x_Lm(1)⁆`,
  `x_Li(f) = ⁅x_Lm(f), x_mi(1)⁆`;
* **degree step** `x_Lm(X^(a+1)) = ⁅x_Li(X^a), x_im(X)⁆` (`k2PolyNagao_good_step`).

So when `|K| ≥ 2`, the goodness of `x_Lm(X)` and of the constants gives `x_Lm(X^k)` for all
`k`, hence (`k2PolyNagao_good_x_of_pow`) `x_Lm(f)` for all `f` (`k2PolyNagao_good_Lm_all`).
When `K = {m}` there is no second index inside `K ∪ {L}`, and all powers `x_Lm(X^k)` are kept.

Truth check: matrix shadows (with signs) over `F_2`, `F_3`, scratchpad `bh-met-92k/chk.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I]
variable {p : ℕ} [Fact p.Prime]

/-- `x_mL(f) = W x_Lm(-f) W⁻¹` is good, from `x_mL(1)`, `x_Lm(-1)` and `x_Lm(-f)`. -/
theorem k2PolyNagao_good_mL {K : Finset I} {L m n : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (h1 : k2PolyEuclid_Good p K L σ (x L m hmL.symm (-1 : Polynomial (ZMod p))))
    {f : Polynomial (ZMod p)} (hf : k2PolyEuclid_Good p K L σ (x L m hmL.symm (-f))) :
    k2PolyEuclid_Good p K L σ (x m L hmL f) := by
  have hW : k2PolyEuclid_Good p K L σ (w m L hmL (1 : (Polynomial (ZMod p))ˣ)) := by
    have e1 : ((1 : (Polynomial (ZMod p))ˣ) : Polynomial (ZMod p)) = 1 := Units.val_one
    have e2 : (((1 : (Polynomial (ZMod p))ˣ)⁻¹ : (Polynomial (ZMod p))ˣ) :
        Polynomial (ZMod p)) = 1 := by
      rw [inv_one, Units.val_one]
    rw [w, e1, e2]
    exact k2PolyEuclid_good_mul (k2PolyEuclid_good_mul hy h1) hy
  have e : x m L hmL f = w m L hmL (1 : (Polynomial (ZMod p))ˣ) * x L m hmL.symm (-f) *
      (w m L hmL (1 : (Polynomial (ZMod p))ˣ))⁻¹ := by
    rw [k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn (1 : (Polynomial (ZMod p))ˣ) (-f)]
    simp only [Units.val_one, one_mul, mul_one, neg_neg]
  rw [e]
  exact k2PolyEuclid_good_mul (k2PolyEuclid_good_mul hW hf) (k2PolyEuclid_good_inv hW)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_mL

/-- `x_iL(f) = ⁅x_im(1), x_mL(f)⁆` is good. -/
theorem k2PolyNagao_good_iL {K : Finset I} {L m i : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (him : i ≠ m) (hiL : i ≠ L)
    (hc : k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))))
    {f : Polynomial (ZMod p)} (hf : k2PolyEuclid_Good p K L σ (x m L hmL f)) :
    k2PolyEuclid_Good p K L σ (x i L hiL f) := by
  have e : x i L hiL f = ⁅x i m him (1 : Polynomial (ZMod p)), x m L hmL f⁆ := by
    rw [x_commutator i m L him hmL hiL, one_mul]
  rw [e]
  exact k2PolyEuclid_good_comm hc hf

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_iL

/-- `x_im(f) = ⁅x_iL(f), x_Lm(1)⁆` is good. -/
theorem k2PolyNagao_good_im {K : Finset I} {L m i : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (him : i ≠ m) (hiL : i ≠ L)
    (h1 : k2PolyEuclid_Good p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))))
    {f : Polynomial (ZMod p)} (hf : k2PolyEuclid_Good p K L σ (x i L hiL f)) :
    k2PolyEuclid_Good p K L σ (x i m him f) := by
  have e : x i m him f = ⁅x i L hiL f, x L m hmL.symm (1 : Polynomial (ZMod p))⁆ := by
    rw [x_commutator i L m hiL hmL.symm him, mul_one]
  rw [e]
  exact k2PolyEuclid_good_comm hf h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_im

/-- `x_Li(f) = ⁅x_Lm(f), x_mi(1)⁆` is good. -/
theorem k2PolyNagao_good_Li {K : Finset I} {L m i : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (him : i ≠ m) (hLi : L ≠ i)
    (hc : k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    {f : Polynomial (ZMod p)} (hf : k2PolyEuclid_Good p K L σ (x L m hmL.symm f)) :
    k2PolyEuclid_Good p K L σ (x L i hLi f) := by
  have e : x L i hLi f = ⁅x L m hmL.symm f, x m i him.symm (1 : Polynomial (ZMod p))⁆ := by
    rw [x_commutator L m i hmL.symm him.symm hLi, mul_one]
  rw [e]
  exact k2PolyEuclid_good_comm hf hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_Li

/-- **Degree step.**  With a second index `i ∈ K \ {m}`: if the constants and `x_Lm(X)` are
good, then every `x_Lm(X^k)` is good, by `x_Lm(X^(a+1)) = ⁅x_Li(X^a), x_im(X)⁆`. -/
theorem k2PolyNagao_good_Lm_pow_of_two {K : Finset I} {L m n i : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n) (him : i ≠ m) (hiL : i ≠ L)
    (hc1 : k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))))
    (hc2 : k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (h1 : k2PolyEuclid_Good p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))))
    (hX : k2PolyEuclid_Good p K L σ (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p)))) :
    ∀ k : ℕ, k2PolyEuclid_Good p K L σ
      (x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ k)) := by
  have hmX : k2PolyEuclid_Good p K L σ (x m L hmL (Polynomial.X : Polynomial (ZMod p))) :=
    k2PolyNagao_good_mL hmL hmn hLn hy (k2PolyNagao_good_x_neg hmL.symm h1)
      (k2PolyNagao_good_x_neg hmL.symm hX)
  have himX : k2PolyEuclid_Good p K L σ (x i m him (Polynomial.X : Polynomial (ZMod p))) :=
    k2PolyNagao_good_im hmL him hiL h1 (k2PolyNagao_good_iL hmL him hiL hc1 hmX)
  intro k
  induction k with
  | zero =>
    rw [pow_zero]
    exact h1
  | succ a ih =>
    have e : x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ (a + 1)) =
        ⁅x L i hiL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ a),
          x i m him (Polynomial.X : Polynomial (ZMod p))⁆ := by
      rw [x_commutator L i m hiL.symm him hmL.symm, pow_succ]
    rw [e]
    exact k2PolyEuclid_good_comm (k2PolyNagao_good_Li hmL him hiL.symm hc2 ih) himX

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_Lm_pow_of_two

/-- **The family `x_Lm(·)` from monomial data.**  If the constants `x_im(1)`, `x_mi(1)`
(`i ∈ K \ {m}`), `x_mL(1)`, `x_Lm(1)` and the root `x_Lm(X)` are good, and, when `K = {m}`,
every `x_Lm(X^k)` is good, then `x_Lm(f)` is good for every `f`. -/
theorem k2PolyNagao_good_Lm_all {K : Finset I} {L m n : I} (hLK : L ∉ K)
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hS : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (h1 : k2PolyEuclid_Good p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))))
    (hX : k2PolyEuclid_Good p K L σ (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))))
    (hsing : (∀ i ∈ K, i = m) → ∀ k : ℕ, k2PolyEuclid_Good p K L σ
      (x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ k)))
    (f : Polynomial (ZMod p)) : k2PolyEuclid_Good p K L σ (x L m hmL.symm f) := by
  refine k2PolyNagao_good_x_of_pow hmL.symm ?_ f
  by_cases hK : ∀ i ∈ K, i = m
  · exact hsing hK
  · obtain ⟨i, hiK, him⟩ : ∃ i ∈ K, i ≠ m := by
      by_contra hne
      exact hK fun i hi => Classical.byContradiction fun h => hne ⟨i, hi, h⟩
    have hiL : i ≠ L := fun e => hLK (e ▸ hiK)
    exact k2PolyNagao_good_Lm_pow_of_two hmL hmn hLn him hiL (hS i him hiK).1
      (hS i him hiK).2 hy h1 hX

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_good_Lm_all

end GroupApproximation.BooneHigman.Metabelian.ElemFP
