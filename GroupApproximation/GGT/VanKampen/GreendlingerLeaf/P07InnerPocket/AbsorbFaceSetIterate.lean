import Mathlib.Data.Fintype.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-38: iterating face-set absorption

`FourPieceWitness.absorbFaceSet_iterate` is a generic termination lemma.  Suppose some pair `(F, x)`
with `F` a finset of a finite type satisfies a basic property `B`, or an escape `R` holds.
Suppose also that every basic pair failing a goal property `S` can be replaced by a basic pair
with strictly more elements, or by a basic pair satisfying `S`, or that `R` holds.  Then some basic
pair satisfies `S`, or `R` holds.  The measure is `Fintype.card β - F.card`.

It is the iteration step behind `AbsorbFaceSetStatement`: absorb lobes and lakes into the face set
until the four local step clauses hold.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

/-- **Iterating a strictly growing replacement terminates.** -/
theorem absorbFaceSet_iterate {β : Type*} {γ : Type*} [Fintype β]
    {B S : Finset β → γ → Prop} {R : Prop}
    (hbase : (∃ F x, B F x) ∨ R)
    (hstep : ∀ F x, B F x → ¬ S F x →
      (∃ F' x', B F' x' ∧ (F.card < F'.card ∨ S F' x')) ∨ R) :
    (∃ F x, B F x ∧ S F x) ∨ R := by
  by_cases hR : R
  · exact Or.inr hR
  · refine Or.inl ?_
    have key : ∀ n : ℕ, ∀ F x, B F x → Fintype.card β - F.card ≤ n →
        ∃ F' x', B F' x' ∧ S F' x' := by
      intro n
      induction n with
      | zero =>
        intro F x hB hn
        by_cases hS : S F x
        · exact ⟨F, x, hB, hS⟩
        · rcases hstep F x hB hS with ⟨F', x', hB', hlt | hS'⟩ | hR'
          · have hle := Finset.card_le_univ F'
            exfalso
            omega
          · exact ⟨F', x', hB', hS'⟩
          · exact absurd hR' hR
      | succ n ih =>
        intro F x hB hn
        by_cases hS : S F x
        · exact ⟨F, x, hB, hS⟩
        · rcases hstep F x hB hS with ⟨F', x', hB', hlt | hS'⟩ | hR'
          · have hle := Finset.card_le_univ F'
            exact ih F' x' hB' (by omega)
          · exact ⟨F', x', hB', hS'⟩
          · exact absurd hR' hR
    rcases hbase with ⟨F, x, hB⟩ | hR'
    · exact key _ F x hB le_rfl
    · exact absurd hR' hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_iterate

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
