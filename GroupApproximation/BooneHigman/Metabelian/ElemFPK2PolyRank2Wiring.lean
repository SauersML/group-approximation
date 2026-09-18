import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyRank2Section
import GroupApproximation.Meta.AxiomGuard

/-!
# Repairing the degree-reduction route for `K₂(F_p[X])`: induction and endpoints

Lane `bh-met-91z`.  These mirror the `_of_amalgam` endpoints of `ElemFPK2PolyDegAmalgam`, with
the refuted `k2PolyDeg_AmalgamStatement` replaced by `k2PolyRank2_SectionStatement`.

* `k2PolyRank2_S_eq_one`: by induction on `K`, `S_K ∩ K₂ = 1` for every finset `K`.
* `k2PolyRank2_K2_eq_bot`: `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.
* `k2PolyRank2_const`: `k2PolyField_ConstStatement (ZMod p) N` for `N ≥ 5`.
* `k2PolyRank2_level_zero`: `nk2Slice_LevelStatement (ZMod p) 0` for every prime `p`.

**LOUD.**  The residual is true but, under the hypotheses it grants, *equivalent* to the
inductive step; see the docstring of `ElemFPK2PolyRank2Section`.  These endpoints are not
vacuous (unlike the `_of_amalgam` ones), but they are conditional on a residual as strong as
`K₂(N, F_p[X]) = ⊥` itself.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction rootSpan_mono mem_rootSpan_true)

section Induction

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **The induction.**  Given the residual and `C(St_I(F_p)) ∩ K₂ = 1` (with `|I| ≥ 3`),
`S_K ∩ K₂ = 1` for every finset `K`. -/
theorem k2PolyRank2_S_eq_one (hSec : k2PolyRank2_SectionStatement)
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
      exact k2PolyRank2_step hSec hmL hmn hLn hLK hmK hthird hC ih hs hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_S_eq_one

end Induction

section Endpoints

/-- The residual kills every element of `K₂(N, F_p[X])`, `N ≥ 5`. -/
theorem k2PolyRank2_eq_one (hSec : k2PolyRank2_SectionStatement) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (hN : 5 ≤ N) {g : St N (Polynomial (ZMod p))}
    (hg : g ∈ K2n N (Polynomial (ZMod p))) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hthird : ∀ a b : Fin N, ∃ k, a ≠ k ∧ b ≠ k :=
    FieldK2.bruhatBigCell_third (by rw [Fintype.card_fin]; omega)
  have hS : g ∈ k2PolyDeg_S p (Finset.univ : Finset (Fin N)) :=
    rootSpan_mono (p := fun _ _ : Fin N => True)
      (q := fun i j => i ∈ (Finset.univ : Finset (Fin N)) ∧ j ∈ (Finset.univ : Finset (Fin N)))
      (fun i j _ _ => ⟨Finset.mem_univ i, Finset.mem_univ j⟩) (mem_rootSpan_true g)
  exact k2PolyRank2_S_eq_one hSec hthird
    (fun z hz hzK => k2PolyField_eq_one_of_mem_range hp hN hzK hz) Finset.univ g hS hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_eq_one

/-- **Endpoint.**  The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyRank2_K2_eq_bot (hSec : k2PolyRank2_SectionStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hg => k2PolyRank2_eq_one hSec hp hN hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_K2_eq_bot

/-- **Endpoint.**  The residual gives `k2PolyField_ConstStatement (ZMod p) N` for every prime
`p` and `N ≥ 5`. -/
theorem k2PolyRank2_const (hSec : k2PolyRank2_SectionStatement) :
    ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N → k2PolyField_ConstStatement (ZMod p) N := by
  intro p hp N hN g hg
  rw [k2PolyRank2_eq_one hSec hp hN hg]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_const

/-- **Endpoint (wiring).**  The residual gives `nk2Slice_LevelStatement (ZMod p) 0` for every
prime `p`, through `ElemFPCharZero.k2PolyField_level_zero_of_const`. -/
theorem k2PolyRank2_level_zero (hSec : k2PolyRank2_SectionStatement) :
    ∀ p : ℕ, p.Prime → ElemFPCharZero.nk2Slice_LevelStatement (ZMod p) 0 :=
  ElemFPCharZero.k2PolyField_level_zero_of_const fun p hp =>
    k2PolyRank2_const hSec p hp 5 le_rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_level_zero

end Endpoints

end GroupApproximation.BooneHigman.Metabelian.ElemFP
