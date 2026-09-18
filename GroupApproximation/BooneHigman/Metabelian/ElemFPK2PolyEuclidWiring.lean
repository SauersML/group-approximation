import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyEuclidRoots
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal forms for `K₂(F_p[X])`: the small-generator residual and its wiring

Lane `bh-met-92h`, part 3.

* `k2PolyEuclid_Gens`: the coset checks for the small generating set of `G` (fixed `m ∈ K`).
  These are `x_im(1)`, `x_mi(1)` (`i ∈ K \ {m}`), `x_mL(1)`, and `x_Lm(f)` for all `f`.
* `k2PolyEuclid_GenStatement` (**the residual**): with the hypotheses of
  `k2PolyNF_CosetStatement`, some `σ` has `σ(e_L) ∈ Q` and satisfies `k2PolyEuclid_Gens` for
  some `m ∈ K`.
* `k2PolyEuclid_coset_of_gen` (generation, `k2PolyEuclid_good_all`) and
  `k2PolyEuclid_gen_of_coset` (the checks are a sub-list): residual `↔` coset criterion.
* `k2PolyEuclid_stab_of_gen`, `k2PolyEuclid_K2_eq_bot_of_gen`: the residual gives the
  stabiliser statement of lane 92c and `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD: EQUIVALENT IN LOGICAL STRENGTH to `k2PolyNF_CosetStatement`, but STRICTLY SMALLER IN
PROOF CONTENT.**  The residual needs `2|K| - 1` constant coset checks and one polynomial family
(`x_Lm(f)`), instead of every root family `x_ij(a)`, `i, j ∈ K ∪ {L}`.  It is TRUE, because it
is equivalent to lane 92c's `k2PolyNF_StabStatement`, which follows from the true
`K₂(N, F_p[X]) = 0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The coset checks for the small generating set of `G`: `x_im(1)` and `x_mi(1)`
(`i ∈ K \ {m}`), `x_mL(1)`, and `x_Lm(f)` for every `f ∈ F_p[X]`. -/
def k2PolyEuclid_Gens (p : ℕ) [Fact p.Prime] (K : Finset I) (L : I)
    (σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))) (m : I)
    (hmL : m ≠ L) : Prop :=
  (∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Check p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Check p K L σ (x m i him.symm (1 : Polynomial (ZMod p)))) ∧
    k2PolyEuclid_Check p K L σ (x m L hmL (1 : Polynomial (ZMod p))) ∧
    ∀ f : Polynomial (ZMod p), k2PolyEuclid_Check p K L σ (x L m hmL.symm f)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_Gens

/-- **The residual.**  The van der Waerden criterion of `k2PolyNF_CosetStatement`, with
the coset check asked only for the small generating set `k2PolyEuclid_Gens`.  TRUE; LOUD:
equivalent to `k2PolyNF_CosetStatement`, strictly smaller in proof content (module docstring).
-/
def k2PolyEuclid_GenStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I),
    L ∉ K → K.Nonempty → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    ∃ σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p)),
      σ (unitVec L) ∈ k2PolyNF_Q p K L ∧
      ∃ (m : I) (hmL : m ≠ L), m ∈ K ∧ k2PolyEuclid_Gens p K L σ m hmL

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_GenStatement

/-- **Reduction.**  The residual gives the van der Waerden criterion of lane 92c. -/
theorem k2PolyEuclid_coset_of_gen (hR : k2PolyEuclid_GenStatement) :
    k2PolyNF_CosetStatement := by
  intro p _ I _ _ K L hLK hK hthird hconst ih
  obtain ⟨σ, hσ, m, hmL, hmK, hG⟩ := hR p K L hLK hK hthird hconst ih
  obtain ⟨hS, hy, hLm⟩ := hG
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
  have hLmg : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f) :=
    fun f => ⟨k2PolyEuclid_x_mem_G hmL.symm f hL' hm', hLm f⟩
  refine ⟨σ, hσ, fun i j hij a hi hj v hv => ?_⟩
  exact (k2PolyEuclid_good_all hLK hmL hmn hLn hSg hyg hLmg i j hij a hi hj).2 v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_coset_of_gen

/-- **Converse.**  The checks of the residual are a sub-list of the criterion. -/
theorem k2PolyEuclid_gen_of_coset (hCo : k2PolyNF_CosetStatement) :
    k2PolyEuclid_GenStatement := by
  intro p _ I _ _ K L hLK hK hthird hconst ih
  obtain ⟨σ, hσ, hgen⟩ := hCo p K L hLK hK hthird hconst ih
  obtain ⟨m, hmK⟩ := hK
  have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
  have hm' : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hL' : L ∈ insert L K := Finset.mem_insert_self L K
  refine ⟨σ, hσ, m, hmL, hmK, fun i him hiK => ⟨?_, ?_⟩, ?_, fun f => ?_⟩
  · exact hgen i m him 1 (Finset.mem_insert_of_mem hiK) hm'
  · exact hgen m i him.symm 1 hm' (Finset.mem_insert_of_mem hiK)
  · exact hgen m L hmL 1 hm' hL'
  · exact hgen L m hmL.symm f hL' hm'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_gen_of_coset

/-- **Endpoint.**  The residual gives lane 92c's stabiliser statement. -/
theorem k2PolyEuclid_stab_of_gen (hR : k2PolyEuclid_GenStatement) :
    k2PolyNF_StabStatement :=
  k2PolyNF_stab_of_coset (k2PolyEuclid_coset_of_gen hR)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_stab_of_gen

/-- **Endpoint.**  The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyEuclid_K2_eq_bot_of_gen (hR : k2PolyEuclid_GenStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNF_K2_eq_bot_of_coset (k2PolyEuclid_coset_of_gen hR) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_K2_eq_bot_of_gen

end GroupApproximation.BooneHigman.Metabelian.ElemFP
