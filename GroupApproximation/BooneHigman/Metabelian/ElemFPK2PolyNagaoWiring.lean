import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoStep
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyEuclidWiring
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao-style normal forms for `K₂(F_p[X])`, part 3: the monomial residual and its wiring

Lane `bh-met-92k`.  Notation of `ElemFPK2PolyEuclidGen`.

* `k2PolyNagao_Gens`: the coset checks for the constant roots `x_im(1)`, `x_mi(1)`
  (`i ∈ K \ {m}`), `x_mL(1)`, `x_Lm(1)`, the single root `x_Lm(X)`, and, **only when
  `K = {m}`**, the monomial roots `x_Lm(X^k)`, `k : ℕ`.
* `k2PolyNagao_MonoStatement` (**the residual**): with the hypotheses of
  `k2PolyEuclid_GenStatement`, some `σ` has `σ(e_L) ∈ Q` and satisfies `k2PolyNagao_Gens`.
* `k2PolyNagao_gen_of_mono`: the residual gives `k2PolyEuclid_GenStatement`
  (`k2PolyNagao_good_Lm_all`: additivity, `c X^k = c.val • X^k`, and for `|K| ≥ 2` the degree
  step `x_Lm(X^(a+1)) = ⁅x_Li(X^a), x_im(X)⁆`).
* `k2PolyNagao_mono_of_gen`: the converse (the checks are a sub-list).
* `k2PolyNagao_stab_of_mono`, `k2PolyNagao_K2_eq_bot_of_mono`: the residual gives lane 92c's
  `k2PolyNF_StabStatement` and `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD: EQUIVALENT IN LOGICAL STRENGTH to `k2PolyEuclid_GenStatement` (both directions are
proved here), STRICTLY SMALLER IN PROOF CONTENT.**  The family `x_Lm(f)`, `f ∈ F_p[X]`
arbitrary, is replaced by:
- for `|K| ≥ 2`: the one polynomial root `x_Lm(X)` (all other checks are constant roots);
- for `K = {m}` (the rank-one step, where `K ∪ {L}` has no third index and the Nagao
  amalgam `SL₂(F_p[X]) = SL₂(F_p) *_{B(F_p)} B(F_p[X])` is the real content): the monomials
  `x_Lm(X^k)`, i.e. no general polynomial coefficients.
The explicit Euclidean `σ` and its coset checks were NOT constructed in Lean.

**Truth.**  TRUE, since it is equivalent to `k2PolyEuclid_GenStatement`, which is equivalent
to lane 92c's `k2PolyNF_StabStatement` (true, as `K₂(N, F_p[X]) = 0` for `N ≥ 5`).  The matrix
shadows of the identities used were checked over `F_2`, `F_3` (scratchpad `bh-met-92k/chk.py`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The coset checks of the monomial residual (fixed `m ∈ K`): the constants `x_im(1)`,
`x_mi(1)` (`i ∈ K \ {m}`), `x_mL(1)`, `x_Lm(1)`, the root `x_Lm(X)`, and, when `K = {m}`,
every `x_Lm(X^k)`. -/
def k2PolyNagao_Gens (p : ℕ) [Fact p.Prime] (K : Finset I) (L : I)
    (σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))) (m : I)
    (hmL : m ≠ L) : Prop :=
  (∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Check p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Check p K L σ (x m i him.symm (1 : Polynomial (ZMod p)))) ∧
    k2PolyEuclid_Check p K L σ (x m L hmL (1 : Polynomial (ZMod p))) ∧
    k2PolyEuclid_Check p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))) ∧
    k2PolyEuclid_Check p K L σ (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))) ∧
    ((∀ i ∈ K, i = m) → ∀ k : ℕ,
      k2PolyEuclid_Check p K L σ (x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ k)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_Gens

/-- **The residual.**  `k2PolyEuclid_GenStatement` with the family `x_Lm(f)` cut down to
`x_Lm(1)`, `x_Lm(X)` (and the monomials `x_Lm(X^k)` when `K = {m}`).  TRUE; LOUD: equivalent
to `k2PolyEuclid_GenStatement`, strictly smaller in proof content (module docstring). -/
def k2PolyNagao_MonoStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I),
    L ∉ K → K.Nonempty → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    ∃ σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p)),
      σ (unitVec L) ∈ k2PolyNF_Q p K L ∧
      ∃ (m : I) (hmL : m ≠ L), m ∈ K ∧ k2PolyNagao_Gens p K L σ m hmL

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_MonoStatement

/-- **Reduction.**  The monomial residual gives `k2PolyEuclid_GenStatement`. -/
theorem k2PolyNagao_gen_of_mono (hM : k2PolyNagao_MonoStatement) :
    k2PolyEuclid_GenStatement := by
  intro p _ I _ _ K L hLK hK hthird hconst ih
  obtain ⟨σ, hσ, m, hmL, hmK, hS, hy, h1, hX, hsing⟩ := hM p K L hLK hK hthird hconst ih
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  have hm' : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hL' : L ∈ insert L K := Finset.mem_insert_self L K
  have hSg : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))) :=
    fun i him hiK =>
      ⟨⟨k2PolyEuclid_x_mem_G him 1 (Finset.mem_insert_of_mem hiK) hm', (hS i him hiK).1⟩,
        ⟨k2PolyEuclid_x_mem_G him.symm 1 hm' (Finset.mem_insert_of_mem hiK),
          (hS i him hiK).2⟩⟩
  have hyg : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL 1 hm' hL', hy⟩
  have h1g : k2PolyEuclid_Good p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL.symm 1 hL' hm', h1⟩
  have hXg : k2PolyEuclid_Good p K L σ
      (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL.symm _ hL' hm', hX⟩
  have hsg : (∀ i ∈ K, i = m) → ∀ k : ℕ, k2PolyEuclid_Good p K L σ
      (x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ k)) :=
    fun hs k => ⟨k2PolyEuclid_x_mem_G hmL.symm _ hL' hm', hsing hs k⟩
  refine ⟨σ, hσ, m, hmL, hmK, hS, hy, fun f => ?_⟩
  exact (k2PolyNagao_good_Lm_all hLK hmL hmn hLn hSg hyg h1g hXg hsg f).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_gen_of_mono

/-- **Converse.**  The checks of the monomial residual are a sub-list of those of
`k2PolyEuclid_GenStatement`. -/
theorem k2PolyNagao_mono_of_gen (hR : k2PolyEuclid_GenStatement) :
    k2PolyNagao_MonoStatement := by
  intro p _ I _ _ K L hLK hK hthird hconst ih
  obtain ⟨σ, hσ, m, hmL, hmK, hS, hy, hLm⟩ := hR p K L hLK hK hthird hconst ih
  exact ⟨σ, hσ, m, hmL, hmK, hS, hy, hLm 1, hLm _, fun _ _ => hLm _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_mono_of_gen

/-- **Endpoint.**  The monomial residual gives lane 92c's stabiliser statement. -/
theorem k2PolyNagao_stab_of_mono (hM : k2PolyNagao_MonoStatement) :
    k2PolyNF_StabStatement :=
  k2PolyEuclid_stab_of_gen (k2PolyNagao_gen_of_mono hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_stab_of_mono

/-- **Endpoint.**  The monomial residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagao_K2_eq_bot_of_mono (hM : k2PolyNagao_MonoStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyEuclid_K2_eq_bot_of_gen (k2PolyNagao_gen_of_mono hM) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagao_K2_eq_bot_of_mono

end GroupApproximation.BooneHigman.Metabelian.ElemFP
