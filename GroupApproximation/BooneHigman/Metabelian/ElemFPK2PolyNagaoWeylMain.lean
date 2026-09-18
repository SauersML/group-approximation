import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylEq
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoSigmaWiring
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 8: `k2PolyNagaoSigma_WeylStatement`, proved outright

Lane `bh-met-93d`.  Notation of `ElemFPK2PolyNagaoWeylLt`.

* `k2PolyNagaoWeyl_check_pair`: for a coprime column `(a, b)` with `deg b ≤ deg a`, the check
  element `(pair (-b) a)⁻¹ W pair a b` lies in `Q`: the cases `b = 0`, `deg b < deg a`
  (`ElemFPK2PolyNagaoWeylLt`) and `deg b = deg a` (`ElemFPK2PolyNagaoWeylEq`).
* `k2PolyNagaoWeyl_check_W`: the same at `σ`, via `W (a, b) = (-b, a)`.
* `k2PolyNagaoWeyl_weylStatement : k2PolyNagaoSigma_WeylStatement`, outright.  The proof uses
  only the explicit words of `σ` (well-founded recursion on the degree, and torus equivariance
  `k2PolyNagaoWeyl_torus_mul_pair` by well-founded induction on the degree), the Steinberg
  relations and Euclidean division in `F_p[X]`.  It does not use the constant-`K₂` hypothesis,
  nor any amalgam decomposition of `SL₂(F_p[X])`.
* `k2PolyNagaoWeyl_K2_bot_of_wide`: hence `k2PolyNagaoSigma_WideStatement` alone gives
  `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD.**  `k2PolyNagaoSigma_WideStatement` is NOT proved or reduced here.  It is the
`|K| ≥ 2` case of `k2PolyNagao_MonoStatement`, unchanged, and remains the whole residual.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act)

section Checks

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

include hmn hLn

/-- The Weyl check element at a coprime column `(a, b)` with `deg b ≤ deg a` lies in `Q`. -/
theorem k2PolyNagaoWeyl_check_pair {K : Finset I} (hmK : m ∈ K) {a b : Polynomial (ZMod p)}
    (hab : IsCoprime a b) (hd : b.degree ≤ a.degree) :
    (k2PolyNagaoSigma_pair p m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
      k2PolyNagaoSigma_pair p m L hmL a b ∈ k2PolyNF_Q p K L := by
  by_cases hb : b = 0
  · subst hb
    rw [k2PolyNagaoWeyl_check_pair_zero hmL hmn hLn (isCoprime_zero_right.1 hab)]
    exact (k2PolyNF_Q p K L).one_mem
  · by_cases hlt : b.degree < a.degree
    · rw [k2PolyNagaoWeyl_check_pair_lt hmL hmn hLn hab hb hlt]
      exact (k2PolyNF_Q p K L).one_mem
    · exact k2PolyNagaoWeyl_check_pair_eq hmL hmn hLn hmK hab hb
        (le_antisymm hd (not_lt.1 hlt))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_check_pair

/-- The Weyl check of `σ` at a vector with coprime `(m, L)` coordinates and
`deg v L ≤ deg v m`. -/
theorem k2PolyNagaoWeyl_check_W {K : Finset I} (hmK : m ∈ K) (v : I → Polynomial (ZMod p))
    (hcop : IsCoprime (v m) (v L)) (hd : (v L).degree ≤ (v m).degree) :
    (k2PolyNagaoSigma_sigma p m L hmL (act (w m L hmL (-1 : (Polynomial (ZMod p))ˣ)) v))⁻¹ *
        w m L hmL (-1 : (Polynomial (ZMod p))ˣ) * k2PolyNagaoSigma_sigma p m L hmL v ∈
      k2PolyNF_Q p K L := by
  obtain ⟨e1, e2⟩ := k2PolyNagaoSigma_act_W hmL v
  rw [k2PolyNagaoSigma_sigma, k2PolyNagaoSigma_sigma, e1, e2]
  exact k2PolyNagaoWeyl_check_pair hmL hmn hLn hmK hcop hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_check_W

end Checks

/-- **`k2PolyNagaoSigma_WeylStatement`, outright.** -/
theorem k2PolyNagaoWeyl_weylStatement : k2PolyNagaoSigma_WeylStatement := by
  intro p _ I _ _ K m L hmL hmK hKm hthird _ v hv hd
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  exact k2PolyNagaoWeyl_check_W hmL hmn hLn hmK v (k2PolyNagaoWeyl_coprime_orbit hmL hKm hv) hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_weylStatement

/-- `k2PolyNagaoSigma_WideStatement` alone gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoWeyl_K2_bot_of_wide (hW : k2PolyNagaoSigma_WideStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoSigma_K2_bot_of_stmt ⟨hW, k2PolyNagaoWeyl_weylStatement⟩ hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_K2_bot_of_wide

end GroupApproximation.BooneHigman.Metabelian.ElemFP
