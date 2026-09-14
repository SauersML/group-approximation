import Mathlib.Tactic.DeriveCountable
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Continuum many Turing degrees

Section "Word problems" of `simple_kazhdan_sofic_group.tex` (origin tip e80dcf20a), proof, last
sentence:

> There are continuum many degrees, ...

This module proves `PrintedContinuumManyDegrees`: there is a family of continuum many sets of
naturals whose characteristic functions are pairwise Turing inequivalent.

The route: oracle programs form a countable type `OCode`, and every function recursive in `g` is
the evaluation of some program at `g`. So the sets reducible to a fixed set are countable, every
Turing class of sets is countable, and the quotient of `Set ℕ` by Turing equivalence has cardinality
`𝔠`. A choice of representatives is the family.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuumManyDegrees

/-- Oracle programs: the constructors of `Nat.RecursiveIn`, with one oracle symbol. -/
inductive OCode where
  | zero
  | succ
  | left
  | right
  | oracle
  | pair (c d : OCode)
  | comp (c d : OCode)
  | prec (c d : OCode)
  | rfind (c : OCode)
  deriving Countable

/-- Evaluation of an oracle program at the oracle `g`, clause by clause as in `Nat.RecursiveIn`. -/
def OCode.eval (g : ℕ →. ℕ) : OCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => g
  | .pair c d => fun n => (Nat.pair <$> c.eval g n <*> d.eval g n)
  | .comp c d => fun n => d.eval g n >>= c.eval g
  | .prec c d => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (c.eval g a) fun y IH => do
        let i ← IH
        d.eval g (Nat.pair a (Nat.pair y i))
  | .rfind c => fun a => Nat.rfind fun n => (fun m => m = 0) <$> c.eval g (Nat.pair a n)

/-- Every function recursive in `g` is the evaluation of an oracle program at `g`. -/
theorem exists_eval_eq {g f : ℕ →. ℕ} (h : Nat.RecursiveIn {g} f) : ∃ c : OCode, c.eval g = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g' hg' =>
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ⟨.oracle, rfl⟩
  | @pair f₁ h₁ _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.pair c d, rfl⟩
  | @comp f₁ h₁ _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.comp c d, rfl⟩
  | @prec f₁ h₁ _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨.prec c d, rfl⟩
  | @rfind f₁ _ ihf =>
    obtain ⟨c, rfl⟩ := ihf
    exact ⟨.rfind c, rfl⟩

/-- The characteristic function of a set determines the set. -/
theorem charOracle_injective : Function.Injective charOracle := by
  intro B C h
  ext n
  have hn := congrFun h n
  simp only [charOracle, Part.some_inj] at hn
  by_cases hB : n ∈ B <;> by_cases hC : n ∈ C <;> simp_all

/-- The sets whose characteristic functions are Turing reducible to a fixed oracle are countable. -/
theorem countable_reducible (g : ℕ →. ℕ) :
    {B : Set ℕ | TuringReducible (charOracle B) g}.Countable := by
  have hsub : {B : Set ℕ | TuringReducible (charOracle B) g} ⊆
      charOracle ⁻¹' Set.range (fun c : OCode => c.eval g) := by
    intro B hB
    obtain ⟨c, hc⟩ := exists_eval_eq (RecursiveIn.iff_nat.1 hB)
    exact ⟨c, hc⟩
  exact ((Set.countable_range _).preimage charOracle_injective).mono hsub

/-- Turing equivalence of characteristic functions, as a setoid on sets of naturals. -/
def degreeSetoid : Setoid (Set ℕ) where
  r B C := TuringEquivalent (charOracle B) (charOracle C)
  iseqv := ⟨fun _ => TuringEquivalent.refl _, fun h => TuringEquivalent.symm h,
    fun h₁ h₂ => TuringEquivalent.trans _ _ _ h₁ h₂⟩

/-- Every Turing class of sets is countable. -/
theorem countable_fiber (q : Quotient degreeSetoid) :
    (Quotient.mk degreeSetoid ⁻¹' {q}).Countable := by
  refine (countable_reducible (charOracle q.out)).mono ?_
  intro C hC
  have hq : Quotient.mk degreeSetoid C = Quotient.mk degreeSetoid q.out := by
    rw [Quotient.out_eq]
    exact hC
  exact And.left (show TuringEquivalent (charOracle C) (charOracle q.out) from Quotient.exact hq)

/-- The quotient of `Set ℕ` by Turing equivalence has cardinality `𝔠`. -/
theorem mk_quotient_degreeSetoid : Cardinal.mk (Quotient degreeSetoid) = Cardinal.continuum := by
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans_eq Cardinal.mk_set_nat
  · by_contra hlt
    rw [not_le] at hlt
    have hmul : Cardinal.mk (Set ℕ) ≤ Cardinal.mk (Quotient degreeSetoid) * Cardinal.aleph0 := by
      refine Cardinal.mk_le_mk_mul_of_mk_preimage_le (Quotient.mk degreeSetoid) fun q => ?_
      haveI := (countable_fiber q).to_subtype
      exact Cardinal.mk_le_aleph0
    rw [Cardinal.mk_set_nat] at hmul
    exact absurd hmul (not_le.2 (Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum hlt
      Cardinal.aleph0_lt_continuum))

/-- **Proof, last sentence.**  There are continuum many Turing degrees of sets of naturals. -/
theorem printedContinuumManyDegrees : PrintedContinuumManyDegrees := by
  refine ⟨Set.range (Quotient.out : Quotient degreeSetoid → Set ℕ), ?_, ?_⟩
  · rw [Cardinal.mk_range_eq _ Quotient.out_injective, mk_quotient_degreeSetoid]
  · rintro _ ⟨q₁, rfl⟩ _ ⟨q₂, rfl⟩ h
    have hq : Quotient.mk degreeSetoid q₁.out = Quotient.mk degreeSetoid q₂.out :=
      Quotient.sound h
    rw [Quotient.out_eq, Quotient.out_eq] at hq
    rw [hq]

#audit_closed_axioms printedContinuumManyDegrees

end ContinuumManyDegrees
end SimpleKazhdanSofic
end GroupApproximation
