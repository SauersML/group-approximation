import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXGroups
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:factorization-nonmf-trace`, sentence by sentence

`non_mf_groups_exist.tex`, Theorem `thm:factorization-nonmf-trace`:

> Let `G` be a countable group.  If `G` is not MF, then its canonical trace
> `τ_G` on `C*_max(G)` is not quasidiagonal.  In particular, if `τ_G` is
> amenable, then `τ_G` is an amenable trace that is not quasidiagonal.

The statement is carried by
`NinetyNineProblems.manuscriptCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF`
and its amenable companion.  This module carries the printed *proof* sentence
by sentence, and records where the tree's proof and the printed proof are two
different routes to the same theorem.

## The route difference, stated up front

The printed proof is constructive in the unitaries: from a quasidiagonal model
`φ_n` it forms the **polar decomposition** of `φ_n(u_g)`, takes its unitary
part `V_n(g)`, and shows the family `V_n` is asymptotically multiplicative and
nondegenerate, which exhibits `G` as MF.

The tree proves the same theorem without ever forming `V_n`:
`Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` turns the quasidiagonal trace
into an MF trace, and `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`
turns that into operator MF-ness by restricting the maps to the canonical group
unitaries and reading off one sufficiently late index
(`Sofic.MFTraceRecognition`).  No polar decomposition occurs anywhere on that
route.

The obstruction to matching the printed route step for step is recorded in the
tree already: `Analysis.CalkinSchauder` notes that "Mathlib has no polar
decomposition of a bounded operator; neither `polarDecomposition` nor
`polar_decomposition` occurs in the library".  Building `V_n` would therefore
mean building the polar decomposition first --- a second proof route alongside
the landed one --- so the four clauses below that mention `V_n` are left
without carriers by design, not by oversight.

## One substitution inside a carried sentence

The printed sentence 2 opens with `φ_n(u_g)^*φ_n(u_g) → 1`.  The adjoint there
is of the *matrix* `φ_n(u_g)`, and identifying it with `φ_n(u_{g⁻¹})` needs
`φ_n` to be `⋆`-preserving, a clause `Quasidiagonal.QuasidiagonalTraceModel`
does not carry (its complete-positivity field is a form-positivity condition,
and its own docstring says nothing in that file consumes it).  So
`manuscriptSentence_nearIsometry` carries the star-free form
`φ_n(u_{g⁻¹}) φ_n(u_g) → 1`, which is what the model actually gives and what
the printed sentence means; the docstring says so.
-/

namespace GroupApproximation
namespace FactorizationTraceSentences

open Filter Matrix Quasidiagonal NinetyNineProblems
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Sentence 1 -/

/-- **Printed sentence 1.**

> Suppose that `τ_G` is quasidiagonal, and let `φ_n` be u.c.p. maps as in the
> definition, with the first limit in operator norm.

Unconditional: unpacking `IsQuasidiagonalTrace` produces exactly the three
clauses the sentence names --- unitality, complete positivity, and asymptotic
multiplicativity in operator norm, which is the "first limit". -/
theorem manuscriptSentence_quasidiagonalModel (G : Type*) [Group G]
    (hqd : IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) :
    ∃ M : QuasidiagonalTraceModel
        (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a),
      (∀ n, M.map n 1 = 1) ∧
        (∀ n, IsCompletelyPositiveOnMatrices (M.space n) ⇑(M.map n)) ∧
        (∀ a b : MaximalGroupCStar G,
          Tendsto (fun n ↦ ‖M.map n (a * b) - M.map n a * M.map n b‖)
            atTop (nhds 0)) := by
  obtain ⟨M⟩ := hqd
  exact ⟨M, M.map_one, M.completelyPositive, M.tendsto_mul⟩

/-! ### Sentence 2 -/

/-- **Printed sentence 2, first clause.**

> Then `φ_n(u_g)^*φ_n(u_g)` and `φ_n(u_g)φ_n(u_g)^*` converge to `1` in
> operator norm …

Carried in the star-free form `φ_n(u_{g⁻¹})φ_n(u_g) → 1` and
`φ_n(u_g)φ_n(u_{g⁻¹}) → 1`.  That is what the model gives: the product
`u_{g⁻¹}u_g` is the unit, `φ_n` is unital, and the maps are asymptotically
multiplicative.  Identifying `φ_n(u_{g⁻¹})` with `φ_n(u_g)^*` needs `φ_n` to
be `⋆`-preserving, which `QuasidiagonalTraceModel` does not assert; see the
module docstring. -/
theorem manuscriptSentence_nearIsometry (G : Type*) [Group G]
    (M : QuasidiagonalTraceModel
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) (g : G) :
    Tendsto (fun n ↦ ‖M.map n (maximalGroupCStarGenerator G g⁻¹) *
        M.map n (maximalGroupCStarGenerator G g) - 1‖) atTop (nhds 0) ∧
      Tendsto (fun n ↦ ‖M.map n (maximalGroupCStarGenerator G g) *
        M.map n (maximalGroupCStarGenerator G g⁻¹) - 1‖) atTop (nhds 0) := by
  have hgen1 : maximalGroupCStarGenerator G (1 : G) = 1 :=
    congrArg (fun w : unitary (MaximalGroupCStar G) ↦ (w : MaximalGroupCStar G))
      (map_one (maximalGroupCStarUnitaryHom G))
  have hleft : maximalGroupCStarGenerator G g⁻¹ *
      maximalGroupCStarGenerator G g = 1 := by
    rw [maximalGroupCStarGenerator_mul, inv_mul_cancel, hgen1]
  have hright : maximalGroupCStarGenerator G g *
      maximalGroupCStarGenerator G g⁻¹ = 1 := by
    rw [maximalGroupCStarGenerator_mul, mul_inv_cancel, hgen1]
  constructor
  · have h := M.tendsto_mul (maximalGroupCStarGenerator G g⁻¹)
      (maximalGroupCStarGenerator G g)
    simp only [hleft, M.map_one] at h
    simpa only [norm_sub_rev] using h
  · have h := M.tendsto_mul (maximalGroupCStarGenerator G g)
      (maximalGroupCStarGenerator G g⁻¹)
    simp only [hright, M.map_one] at h
    simpa only [norm_sub_rev] using h

/-- **Printed sentence 2, third clause.**

> … and `V_n(1) = 1` because `φ_n` is unital.

The unitality of `φ_n` at the identity generator is carried; the reference to
`V_n` is not, since `V_n` is not constructed on this route. -/
theorem manuscriptSentence_unitalAtIdentity (G : Type*) [Group G]
    (M : QuasidiagonalTraceModel
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) (n : ℕ) :
    M.map n (maximalGroupCStarGenerator G (1 : G)) = 1 := by
  have hgen1 : maximalGroupCStarGenerator G (1 : G) = 1 :=
    congrArg (fun w : unitary (MaximalGroupCStar G) ↦ (w : MaximalGroupCStar G))
      (map_one (maximalGroupCStarUnitaryHom G))
  rw [hgen1, M.map_one]

/-! ### Sentence 4 -/

/-- **Printed sentence 4, second clause.**

> … contradicting `tr_{d_n}(φ_n(u_g)) → τ_G(u_g) = 0`.

Unconditional: the trace clause of the model at a nonidentity canonical
unitary, where the canonical trace vanishes. -/
theorem manuscriptSentence_traceTendsToZero (G : Type*) [Group G]
    (M : QuasidiagonalTraceModel
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) {g : G}
    (hg : g ≠ 1) :
    Tendsto (fun n ↦ ‖normTrace (M.space n)
      (M.map n (maximalGroupCStarGenerator G g))‖) atTop (nhds 0) := by
  have h := M.tendsto_trace (maximalGroupCStarGenerator G g)
  simp only [canonicalMaximalTrace_generator_of_ne_one G hg, zero_sub,
    norm_neg] at h
  exact h

/-! ### Sentence 5 -/

/-- **Printed sentence 5, conclusion.**

> … and `G` is MF, contrary to the hypothesis.

Unconditional, and this is the sentence where the two routes rejoin.  The
printed proof reaches it from the nondegeneracy of `V_n`; the tree reaches it
from `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` and
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`.  The carrier is a
wrapper over the landed contrapositive, not a second proof of it. -/
theorem manuscriptSentence_quasidiagonalGivesMF (G : Type*) [Group G]
    (hqd : IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) :
    IsOperatorMF G := by
  by_contra hnot
  exact canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF G
    hnot hqd

/-! ### Sentence 6 -/

/-- **Printed sentence 6.**

> The last assertion follows.

The "last assertion" is the second sentence of the theorem: if `τ_G` is
amenable and `G` is not MF, then `τ_G` is an amenable trace that is not
quasidiagonal.  A one-line alias of the landed carrier. -/
theorem manuscriptSentence_lastAssertion :
    ∀ (G : Type*) [Group G],
      IsAmenableTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
        (¬ IsOperatorMF G) →
          IsAmenableTrace
              (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) ∧
            ¬ IsQuasidiagonalTrace
              (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF

end

end FactorizationTraceSentences
end GroupApproximation

open GroupApproximation

#audit_axioms FactorizationTraceSentences.manuscriptSentence_quasidiagonalModel
#audit_axioms FactorizationTraceSentences.manuscriptSentence_nearIsometry
#audit_axioms FactorizationTraceSentences.manuscriptSentence_unitalAtIdentity
#audit_axioms FactorizationTraceSentences.manuscriptSentence_traceTendsToZero
#audit_axioms FactorizationTraceSentences.manuscriptSentence_quasidiagonalGivesMF
#audit_axioms FactorizationTraceSentences.manuscriptSentence_lastAssertion
