import GroupApproximation.Sofic.ProductMultiplicity
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# The multiplicity family over the literal `E`

`\label{p:mult-products}` prints

> the groups `E × ℤ^k` for `k ≥ 0` are finitely presented, pairwise
> nonisomorphic and non-MF, each containing `E` (Lemma
> \ref{lem:permanence}(1)).

Ledger row `UN.06` graded that MISMATCH/MISMATCH over **substituted** objects,
for two reasons its note states exactly:

1. `ProductMultiplicity.manuscriptInfiniteMultiplicity` builds the family over
   `ChosenMarkedPresentation.MarkedGroup`, the *Chosen* presentation, while the
   printed sentence names the literal eight-generator `E` of `\ref{def:E}`;
2. the clause "each containing `E`" is not among the conjuncts — injectivity of
   `MonoidHom.inl` is used *inside* `not_isOperatorMF_family` and never stated.

Both are closed here, and neither needs new mathematics.  Every piece of the
family machinery in `Sofic/ProductMultiplicity.lean` is generic in the first
factor — `family_finitelyPresented`, `not_isOperatorMF_family`,
`eq_of_family_mulEquiv`, `torsionFreeRank_family`, `card_hom_family` — so the
only input the literal group has to supply is `¬ IsOperatorMF E`, which is
`LiteralNonMFEndpoint.literal_not_isOperatorMF`, together with its finite
presentation.

## The embedding clause

`each containing E` is `MonoidHom.inl`, and stating it costs a conjunct rather
than an argument: the injectivity was already being proved, inside
`not_isOperatorMF_family`, in order to pull non-MF back along it.  A conjunct
that a proof already establishes and the statement omits is precisely the
defect class this row was recording, so it is stated.

`lem:permanence(1)` — MF passes to subgroups — is what makes the printed
sentence's parenthesis a *reason*; here the same fact enters as
`IsOperatorMF.comap` inside `not_isOperatorMF_family`, which is the direction
the argument actually uses.
-/

namespace GroupApproximation
namespace LiteralProductMultiplicity

open ProductMultiplicity ProductFinitePresentation

noncomputable section

open LiteralNonMFPresentation in
/-- The literal family `E × ℤ^k`. -/
abbrev LiteralFamily (k : ℕ) : Type := Family MarkedGroup k

open LiteralNonMFPresentation in
theorem literalFamily_finitelyPresented (k : ℕ) :
    Group.IsFinitelyPresented (LiteralFamily k) :=
  family_finitelyPresented MarkedGroup k

open LiteralNonMFPresentation in
theorem literalFamily_not_isOperatorMF (k : ℕ) :
    ¬ IsOperatorMF (LiteralFamily k) :=
  not_isOperatorMF_family LiteralNonMFEndpoint.literal_not_isOperatorMF k

open LiteralNonMFPresentation in
/-- **"each containing `E`".**  The first-factor inclusion is injective, so
every member of the family contains a copy of the literal `E`. -/
theorem literalFamily_inl_injective (k : ℕ) :
    Function.Injective (MonoidHom.inl MarkedGroup (IntPow k)) := by
  intro a b hab
  simpa using congrArg Prod.fst hab

open LiteralNonMFPresentation in
theorem literalFamily_eq_of_mulEquiv {k l : ℕ}
    (e : LiteralFamily k ≃* LiteralFamily l) : k = l := by
  haveI : Group.FG MarkedGroup := fg_of_isFinitelyPresented MarkedGroup
  exact eq_of_family_mulEquiv e

open LiteralNonMFPresentation in
theorem literalFamily_torsionFreeRank_ne {k l : ℕ} (h : k ≠ l) :
    TorsionFreeRank.abelianizationRank (LiteralFamily k) ≠
      TorsionFreeRank.abelianizationRank (LiteralFamily l) := by
  haveI : Group.FG MarkedGroup := fg_of_isFinitelyPresented MarkedGroup
  intro hEq
  rw [torsionFreeRank_family, torsionFreeRank_family] at hEq
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (TorsionFreeRank.abelianizationRank_lt_aleph0 MarkedGroup)
  rw [hn, ← Nat.cast_add, ← Nat.cast_add] at hEq
  exact h (Nat.add_left_cancel (Nat.cast_injective hEq))

open LiteralNonMFPresentation in
theorem literalFamily_card_hom_ne {k l : ℕ} (h : k ≠ l) :
    Nat.card (LiteralFamily k →* TwoGroup) ≠
      Nat.card (LiteralFamily l →* TwoGroup) := by
  haveI : Group.FG MarkedGroup := fg_of_isFinitelyPresented MarkedGroup
  haveI : Finite (MarkedGroup →* TwoGroup) := finite_hom_of_fg MarkedGroup TwoGroup
  haveI : Nonempty (MarkedGroup →* TwoGroup) := ⟨1⟩
  have hpos : 0 < Nat.card (MarkedGroup →* TwoGroup) := Nat.card_pos
  intro hEq
  rw [card_hom_family, card_hom_family] at hEq
  exact h (Nat.pow_right_injective (le_refl 2)
    (Nat.eq_of_mul_eq_mul_left hpos hEq))

open LiteralNonMFPresentation in
/-- **`UN.06`, the printed sentence, over the literal `E`.**

> the groups `E × ℤ^k` for `k ≥ 0` are finitely presented, pairwise
> nonisomorphic and non-MF, each containing `E`.

The family is `E × ℤ^k` for the literal eight-generator `E`, not the Chosen
presentation, and the embedding clause is a conjunct rather than a step inside
a proof.  The two printed invariants are kept, in the printed order, ahead of
the nonisomorphism they establish: a badge certifying only the last clause
would certify a true statement that is not the printed one. -/
theorem manuscriptInfiniteMultiplicity_literal :
    ∃ ι : ∀ k : ℕ, MarkedGroup →* LiteralFamily k,
      (∀ k, Function.Injective (ι k)) ∧
        (∀ k, Group.IsFinitelyPresented (LiteralFamily k)) ∧
          (∀ k, ¬ IsOperatorMF (LiteralFamily k)) ∧
            (∀ k l, k ≠ l →
              TorsionFreeRank.abelianizationRank (LiteralFamily k) ≠
                TorsionFreeRank.abelianizationRank (LiteralFamily l)) ∧
              (∀ k l, k ≠ l →
                Nat.card (LiteralFamily k →* TwoGroup) ≠
                  Nat.card (LiteralFamily l →* TwoGroup)) ∧
                (∀ k l, Nonempty (LiteralFamily k ≃* LiteralFamily l) → k = l) :=
  ⟨fun k ↦ MonoidHom.inl MarkedGroup (IntPow k),
    literalFamily_inl_injective,
    literalFamily_finitelyPresented,
    literalFamily_not_isOperatorMF,
    fun _ _ h ↦ literalFamily_torsionFreeRank_ne h,
    fun _ _ h ↦ literalFamily_card_hom_ne h,
    fun _ _ ⟨e⟩ ↦ literalFamily_eq_of_mulEquiv e⟩

end

end LiteralProductMultiplicity
end GroupApproximation
