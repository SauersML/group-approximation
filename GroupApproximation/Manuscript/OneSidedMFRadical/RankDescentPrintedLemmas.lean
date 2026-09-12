import GroupApproximation.Leavitt.RankDescentEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# The two new printed lemmas of the rank-two strengthening

`notes/rank-two-descent-note-2026-09-07.md`, §§1–2, in the shape the
manuscript prints them.

The mathematics is `Leavitt.ProperlyInfiniteUnit` and
`Leavitt.RankTwoNormalGeneration`; this module only restates it as two closed
propositions named after the printed labels, so that each printed lemma has a
single Lean target.  The `ProperlyInfiniteUnit` structure is unfolded into bare
data here, because the printed lemma quantifies over elements of `R` and not
over a bundled structure.

## The two lemmas

**New Lemma [two copies].**  For a unital ring, a one-sided pair `ts = 1`
together with a fullness witness for `e = 1 - st` is interchangeable with four
elements `v₀, v₁, w₀, w₁` satisfying `wᵢvⱼ = δᵢⱼ`.

**New Lemma [normal generation in rank two].**  If `wv = 1`, `ba = 1` and
`bv = 0`, then `D = [e₁₂(v), e₂₁(b)]` equals `diag(1+vb, 1)` and normally
generates `EL₂(R)`.

Neither lemma asks for countability, property `(T)`, simplicity, or any
normal-structure input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankDescentPrinted

open RankDescent
open OneSidedCompressor
open scoped commutatorElement

/-! ## New Lemma [two copies] -/

/-- **New Lemma [two copies], as one closed proposition.**  The printed
hypothesis of `thm:full-defect-ring` and a properly infinite unit are the same
data, in either direction.

The note states the equivalence for nonzero `R`; no such hypothesis is needed,
because in the zero ring both sides hold vacuously. -/
def PrintedTwoCopiesLemma : Prop :=
  ∀ (R : Type) [Ring R],
    (∃ (s t : R), t * s = 1 ∧
        ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) ↔
      ∃ v w : Fin 2 → R, ∀ i j, w i * v j = if i = j then 1 else 0

theorem manuscriptTwoCopiesLemma : PrintedTwoCopiesLemma := by
  intro R _
  constructor
  · rintro ⟨s, t, hts, m, a, b, hab⟩
    refine ⟨(ofFull (⟨s, t, hts⟩ : OneSidedInverse R) a b hab).v,
      (ofFull (⟨s, t, hts⟩ : OneSidedInverse R) a b hab).w, ?_⟩
    exact (ofFull (⟨s, t, hts⟩ : OneSidedInverse R) a b hab).w_mul_v
  · rintro ⟨v, w, hvw⟩
    refine ⟨(⟨v, w, hvw⟩ : ProperlyInfiniteUnit R).v 0,
      (⟨v, w, hvw⟩ : ProperlyInfiniteUnit R).w 0,
      (⟨v, w, hvw⟩ : ProperlyInfiniteUnit R).w_mul_v_self 0, ?_⟩
    exact (⟨v, w, hvw⟩ : ProperlyInfiniteUnit R).toOneSidedInverse_isFull

/-! ## New Lemma [normal generation in rank two] -/

/-- **New Lemma [normal generation in rank two], as one closed proposition.**
Both printed assertions: the commutator is the printed diagonal matrix, and it
normally generates.

The coefficient `a` appears only through `ba = 1`, and `w` only through
`wv = 1`; neither is part of the generator. -/
def PrintedRankTwoNormalGeneration : Prop :=
  ∀ (R : Type) [Ring R] (v w a b : R), w * v = 1 → b * a = 1 → b * v = 0 →
    ((gen v b : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
        = 1 + Matrix.single 0 0 (v * b) ∧
      Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R)) = ⊤

theorem manuscriptRankTwoNormalGeneration : PrintedRankTwoNormalGeneration := by
  intro R _ v w a b hwv hba hbv
  exact ⟨gen_val v b hbv, normalClosure_gen_eq_top v w a b hwv hba hbv⟩

/-- The printed generator is the printed commutator, on the nose. -/
theorem gen_eq_printed_commutator {R : Type} [Ring R] (v b : R) :
    gen v b = ⁅upperRoot v, lowerRoot b⁆ := rfl

end RankDescentPrinted
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms RankDescentPrinted.manuscriptTwoCopiesLemma
#audit_closed_axioms RankDescentPrinted.manuscriptRankTwoNormalGeneration
