import GroupApproximation.Sofic.WeakMFUltraproduct
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin's reformulation, along the full sequence

`non_mf_groups_exist.tex`, the introduction (line 98):

> For countable `G`, the second condition may equivalently be required along
> the full sequence with a constant independent of
> `g`~\cite[Propositions~2 and~7]{Korchagin}.

The "second condition" is the separation clause of the printed definition of an
MF group: `limsup_n ‖V_n(g) - 1‖ > 0` for every `g ≠ 1`.  As printed it is a
`limsup`, so the separation may be attained only along a subsequence and the
implicit constant may depend on `g`.  Korchagin's Propositions 2 and 7 say that
for a countable group one may instead demand a **single** constant, valid at
**every** index of the sequence from some point on.

That stronger shape is the tree's `WeakMFApproximation`: a sequence of finite
unitary models carrying one positive `separation` constant, with
`separatedEventually` asserting the bound for every pair of distinct elements
at every large index.  The printed `limsup` shape is `IsOperatorMF`, an
injective homomorphism into the unitary group of the norm matrix corona.

## What was missing

The forward half was already in the tree: `exists_weakMFApproximation`
assembles the local models of a countable group into one sequential
approximation with a fixed constant.  The converse — that a sequential
approximation with a uniform constant is in particular a family of local models
at that constant — had no statement, so the printed *equivalence* could not be
formed.  `isNormApproximable_of_weakMFApproximation` supplies it: for a finite
set `F` and a tolerance `ε`, take the index past the finitely many thresholds
that `F × F` demands, and read the model off there.

With both halves, `manuscriptSentence_korchaginFullSequenceSeparation` states
the printed equivalence itself, with no hypothesis beyond the printed
countability.

## The constant

The printed sentence says "a constant independent of `g`", not "the constant
`1`".  Both are available and they are the same statement: the normalisation to
`1` is `OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one`
(Korchagin's amplification), and the equivalence below keeps the constant
existential, which is the literal printed phrasing.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace KorchaginSentence

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ### A sequential approximation restricts to local models -/

/-- **A sequential weak-MF approximation gives local models at its own
separation constant.**

The converse of `exists_weakMFApproximation`.  Both of the approximation's
clauses are eventual and indexed by a *pair* of group elements, so a finite
`F` imposes only finitely many thresholds; any index past all of them carries
a model of `F` at tolerance `ε`. -/
theorem isNormApproximable_of_weakMFApproximation (A : WeakMFApproximation G) :
    IsNormApproximable G A.separation := by
  classical
  intro F ε hε
  have hmul : ∀ p : G × G, ∃ N : ℕ, ∀ n ≥ N,
      ‖(A.map n (p.1 * p.2) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n p.1 : Matrix (A.model n) (A.model n) ℂ) * A.map n p.2‖ ≤ ε :=
    fun p ↦ A.asymptoticallyMultiplicative p.1 p.2 ε hε
  choose Nmul hNmul using hmul
  have hsep : ∀ p : G × G, ∃ N : ℕ, ∀ n ≥ N, p.1 ≠ p.2 →
      A.separation ≤
        ‖(A.map n p.1 : Matrix (A.model n) (A.model n) ℂ) - A.map n p.2‖ := by
    intro p
    by_cases hne : p.1 = p.2
    · exact ⟨0, fun _ _ h ↦ absurd hne h⟩
    · obtain ⟨N, hN⟩ := A.separatedEventually p.1 p.2 hne
      exact ⟨N, fun n hn _ ↦ hN n hn⟩
  choose Nsep hNsep using hsep
  set S : Finset (G × G) := F ×ˢ F
  set N : ℕ := max (S.sup Nmul) (S.sup Nsep)
  refine ⟨{ carrier := A.model N
            nonempty := A.modelNonempty N
            map := fun g ↦ (A.map N g : Matrix (A.model N) (A.model N) ℂ)
            isUnitary := fun g ↦ (A.map N g).2
            multiplicative := ?_
            separated := ?_ }⟩
  · intro g hg h hh
    refine hNmul (g, h) N ?_
    refine le_trans (Finset.le_sup (f := Nmul) ?_) (le_max_left _ _)
    exact Finset.mem_product.mpr ⟨hg, hh⟩
  · intro g hg h hh hne
    refine hNsep (g, h) N ?_ hne
    refine le_trans (Finset.le_sup (f := Nsep) ?_) (le_max_right _ _)
    exact Finset.mem_product.mpr ⟨hg, hh⟩

/-- A sequential approximation is a weak-MF certificate at its own constant. -/
theorem isWeakMF_of_weakMFApproximation (A : WeakMFApproximation G) :
    IsWeakMF G :=
  ⟨A.separation, A.separation_pos, isNormApproximable_of_weakMFApproximation A⟩

/-! ### The printed sentence -/

/-- **Printed:** "For countable `G`, the second condition may equivalently be
required along the full sequence with a constant independent of
`g`~\cite[Propositions~2 and~7]{Korchagin}."

The left side is the printed definition, whose separation clause is a `limsup`
with a constant that may depend on `g` (injectivity into the corona).  The
right side is a sequence of finite unitary models carrying one positive
separation constant that works for every pair of distinct elements at every
large index. -/
def PrintedKorchaginFullSequenceSeparation : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsOperatorMF G ↔ Nonempty (WeakMFApproximation G)

/-- Closed proof of Korchagin's reformulation.  Forward is
`exists_weakMFApproximation` after normalising the constant to `1`; backward is
the local-model restriction above, fed to `IsWeakMF.isOperatorMF`. -/
theorem manuscriptSentence_korchaginFullSequenceSeparation :
    PrintedKorchaginFullSequenceSeparation := by
  intro G _ _
  constructor
  · intro h
    exact exists_weakMFApproximation zero_lt_one
      (OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mp h)
  · rintro ⟨A⟩
    exact IsWeakMF.isOperatorMF (isWeakMF_of_weakMFApproximation A)

end KorchaginSentence
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.KorchaginSentence.isNormApproximable_of_weakMFApproximation
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation
