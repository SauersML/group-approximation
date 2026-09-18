import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNFStab
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal forms for `K₂(F_p[X])`, part 2: the step, the induction and the endpoints

Lane `bh-met-92c`.  Notation of `ElemFPK2PolyNFStab`.

* `k2PolyNF_step`: the residual `k2PolyNF_StabStatement` gives `G_{K ∪ {L}} ∩ K₂ = 1` from
  `S_K ∩ K₂ = 1`.  An element of `K₂` fixes `e_L`, so it lies in `Q ≤ P`, and
  `k2PolyDeg_eq_one_of_mem_P` (lane 91c) kills it.  The extension theorem and any section of
  `projection` are not used.
* `k2PolyNF_S_eq_one`: induction on `K`.
* `k2PolyNF_K2_eq_bot_of_stab`: `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.
* `k2PolyNF_K2_eq_bot_of_coset`: the same from the van der Waerden criterion.
* `k2PolyNF_const_of_stab`: `k2PolyField_ConstStatement (ZMod p) N` for `N ≥ 5`.

**LOUD.**  The residual is TRUE but, under the hypotheses it grants, EQUIVALENT to the step
(module docstring of `ElemFPK2PolyNFStab`).  These endpoints are conditional on it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction rootSpan_mono mem_rootSpan_true act unitVec act_of_projection_eq_one)

section Induction

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **The inductive step from the residual.** -/
theorem k2PolyNF_step (hS : k2PolyNF_StabStatement) {K : Finset I} {m L n : I}
    (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (hLK : L ∉ K) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (ih : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_G p K L)
    (hK2 : g ∈ K2 I (Polynomial (ZMod p))) : g = 1 := by
  have hfix : act g (unitVec L) = unitVec L :=
    act_of_projection_eq_one ((mem_K2_iff g).mp hK2) (unitVec L)
  have hQ : g ∈ k2PolyNF_Q p K L := hS p K L hLK ⟨m, hmK⟩ hthird hC ih g hg hfix
  have hP : g ∈ k2PolyDeg_P p K m L n hmL hmn hLn := by
    show g ∈ (k2PolyDeg_torus p m L n hmL hmn hLn).range ⊔
      (k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L)
    exact Subgroup.mem_sup_right hQ
  exact k2PolyDeg_eq_one_of_mem_P hmL hmn hLn hLK ih hP hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_step

/-- **The induction.**  Given the residual and `C(St_I(F_p)) ∩ K₂ = 1` (with `|I| ≥ 3`),
`S_K ∩ K₂ = 1` for every finset `K`. -/
theorem k2PolyNF_S_eq_one (hS : k2PolyNF_StabStatement)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) (K : Finset I) :
    ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1 := by
  induction K using Finset.induction_on with
  | empty =>
    intro s hs _
    exact rootSpan_induction (p := fun i j => i ∈ (∅ : Finset I) ∧ j ∈ (∅ : Finset I))
      (Q := fun z => z = 1)
      (fun i j _ _ (hq : i ∈ (∅ : Finset I) ∧ j ∈ (∅ : Finset I)) =>
        absurd hq.1 (Finset.notMem_empty i)) rfl
      (fun g k _ _ h1 h2 => show g * k = 1 by
        rw [show g = 1 from h1, show k = 1 from h2, one_mul]) hs
  | insert L K hLK ih =>
    intro s hs hK2
    rcases Finset.eq_empty_or_nonempty K with hK0 | ⟨m, hmK⟩
    · subst hK0
      have key : ∀ k : I, k ∈ insert L (∅ : Finset I) → k = L := fun k hk =>
        (Finset.mem_insert.mp hk).resolve_right (Finset.notMem_empty k)
      exact rootSpan_induction
        (p := fun i j => i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I))
        (Q := fun z => z = 1)
        (fun i j hij _ (hq : i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I)) =>
          absurd ((key i hq.1).trans (key j hq.2).symm) hij) rfl
        (fun g k _ _ h1 h2 => show g * k = 1 by
          rw [show g = 1 from h1, show k = 1 from h2, one_mul]) hs
    · have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
      obtain ⟨n, hmn, hLn⟩ := hthird m L
      exact k2PolyNF_step hS hmL hmn hLn hLK hmK hthird hC ih hs hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_S_eq_one

end Induction

section Endpoints

/-- The residual kills every element of `K₂(N, F_p[X])`, `N ≥ 5`. -/
theorem k2PolyNF_eq_one_of_stab (hS : k2PolyNF_StabStatement) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (hN : 5 ≤ N) {g : St N (Polynomial (ZMod p))}
    (hg : g ∈ K2n N (Polynomial (ZMod p))) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hthird : ∀ a b : Fin N, ∃ k, a ≠ k ∧ b ≠ k :=
    FieldK2.bruhatBigCell_third (by rw [Fintype.card_fin]; omega)
  have hSK : g ∈ k2PolyDeg_S p (Finset.univ : Finset (Fin N)) :=
    rootSpan_mono (p := fun _ _ : Fin N => True)
      (q := fun i j => i ∈ (Finset.univ : Finset (Fin N)) ∧ j ∈ (Finset.univ : Finset (Fin N)))
      (fun i j _ _ => ⟨Finset.mem_univ i, Finset.mem_univ j⟩) (mem_rootSpan_true g)
  exact k2PolyNF_S_eq_one hS hthird
    (fun z hz hzK => k2PolyField_eq_one_of_mem_range hp hN hzK hz) Finset.univ g hSK hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_eq_one_of_stab

/-- **Endpoint.**  The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNF_K2_eq_bot_of_stab (hS : k2PolyNF_StabStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hg => k2PolyNF_eq_one_of_stab hS hp hN hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_K2_eq_bot_of_stab

/-- **Endpoint.**  The van der Waerden criterion gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNF_K2_eq_bot_of_coset (hCo : k2PolyNF_CosetStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNF_K2_eq_bot_of_stab (k2PolyNF_stab_of_coset hCo) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_K2_eq_bot_of_coset

/-- **Endpoint.**  The residual gives `k2PolyField_ConstStatement (ZMod p) N` for every prime
`p` and `N ≥ 5`. -/
theorem k2PolyNF_const_of_stab (hS : k2PolyNF_StabStatement) :
    ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N → k2PolyField_ConstStatement (ZMod p) N := by
  intro p hp N hN g hg
  rw [k2PolyNF_eq_one_of_stab hS hp hN hg]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_const_of_stab

end Endpoints

end GroupApproximation.BooneHigman.Metabelian.ElemFP
