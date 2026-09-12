import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Sofic.PrintedPreliminaryEstimates
import GroupApproximation.Sofic.UltrafilterLimit
import GroupApproximation.Sofic.OpToHSShadowResidual
import GroupApproximation.Analysis.PrintedCornerCompression
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarTrivialCharacter
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level formalization of `non_mf_groups_exist.tex`, `thm:normal-kazhdan`'s `τ`

`non_mf_groups_exist.tex`, the proof of Theorem `thm:normal-kazhdan` (tex
lines 670-673, as of commit `ed803f4d5`; identified by content, since the
manuscript's line numbers shift with unrelated edits):

> Fix a free ultrafilter `ω` and let `τ` be the limit along `ω` of the
> normalized traces of the coordinates `M_{r_n}(ℂ)`.  A norm-null sequence
> has vanishing traces, since `|tr_{r_n}(x)| ≤ ‖x‖`, so `τ` is a well defined
> tracial state on `𝒬_r`.

`Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean` proves the
theorem's conclusion by a different, ultrafilter-free route (a direct
`limsup` estimate on finite combinations of corner unitaries), and its own
docstring records that "the manuscript's proof was rewritten to avoid
ultrafilters" and that none of the ultrafilter sentences occurs in that
route.  Since the printed text above is still exactly what is on the page,
this module supplies it on its own terms, at the printed generality (any
family of finite models, any free ultrafilter), rather than leaving it
uncarried.

## What `τ` is, and what is reused

`Analysis/TracialMatrixUltraproduct.lean` already builds an ultrafilter-limit
normalized trace `seqUltratrace X ω a := lim_ω tr_{X n}(a n)` on bounded
matrix sequences, together with its full representative-level algebra
(`seqUltratrace_add`, `seqUltratrace_smul`, `seqUltratrace_one`,
`seqUltratrace_mul_comm`, `seqUltratrace_star_mul_self`,
`seqHSLimit_nonneg`) — built for the *Hilbert--Schmidt*-null quotient, but
none of those representative-level facts mentions that quotient at all, so
they are exactly the printed `τ`'s linearity, unit, traciality and
positivity, reused verbatim.  What that file does not supply is
well-definedness against the printed quotient `𝒬_r` (`NormMatrixCStarCorona`,
the *operator-norm*-null quotient): that is genuinely new content, proved
below from the printed bound `|tr_{r_n}(x)| ≤ ‖x‖`
(`PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm`), which is the
easier of the two null-ideal comparisons since it needs no
Hilbert--Schmidt/Cauchy--Schwarz step: an operator-norm-null sequence has
normalized traces tending to `0` directly from that one bound.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## `thm:normal-kazhdan`, proof sentence (tex lines 670-673)

"Fix a free ultrafilter `ω` and let `τ` be the limit along `ω` of the
normalized traces of the coordinates `M_{r_n}(ℂ)`.  A norm-null sequence has
vanishing traces, since `|tr_{r_n}(x)| ≤ ‖x‖`, so `τ` is a well defined
tracial state on `𝒬_r`." -/

/-- **The printed `τ` is well defined on `𝒬_r`.**  Two bounded matrix
sequences representing the same class of the operator-norm corona
`NormMatrixCStarCorona` have the same ultrafilter-limit normalized trace: the
printed argument, verbatim.  A representative of the zero class is
operator-norm-null along `cofinite`; freeness of `ω`
(`(ω : Filter ℕ) ≤ cofinite`) transports that to `ω`, and
`|tr_{r_n}(x)| ≤ ‖x‖` squeezes the trace difference to `0` along `ω`, so the
two ultrafilter limits agree by uniqueness of limits. -/
theorem manuscriptSentence_ultrafilterNormalizedTraceWellDefined
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    {a b : BoundedMatrixSequence (fun n ↦ X n)}
    (h : normMatrixCStarCoronaMk (fun n ↦ X n) a
        = normMatrixCStarCoronaMk (fun n ↦ X n) b) :
    TracialUltraproduct.seqUltratrace X ω a
      = TracialUltraproduct.seqUltratrace X ω b := by
  have hmk0 : normMatrixCStarCoronaMk (fun n ↦ X n) (a - b) = 0 := by
    rw [RingHom.map_sub (normMatrixCStarCoronaMk (fun n ↦ X n)) a b, h, sub_self]
  have hnullCofinite : Tendsto (fun n ↦ ‖(a - b) n‖) cofinite (nhds 0) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) (a - b)).mp hmk0
  have hnullOmega : Tendsto (fun n ↦ ‖(a - b) n‖) (ω : Filter ℕ) (nhds 0) :=
    hnullCofinite.mono_left hω
  have hzero : Tendsto
      (fun n ↦ normTrace (X n) (a n) - normTrace (X n) (b n))
      (ω : Filter ℕ) (nhds 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hnullOmega
    rw [← normTrace_sub (X n) (a n) (b n)]
    exact PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (X n)
      ((a - b) n)
  have hdiff := (TracialUltraproduct.tendsto_seqUltratrace X ω a).sub
    (TracialUltraproduct.tendsto_seqUltratrace X ω b)
  have huniq := tendsto_nhds_unique hdiff hzero
  linear_combination huniq

/-- **`τ` is a well defined tracial state on `𝒬_r`, as one closed
proposition.**  Every clause of the printed sentence, at representatives of
`𝒬_r = NormMatrixCStarCorona`: well-definedness against the corona class,
linearity, the unit, positivity (`τ(a*a)` is a nonnegative real), and
traciality (`τ(ab) = τ(ba)`). -/
def UltrafilterNormalizedTraceIsWellDefinedTracialState : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ),
    (ω : Filter ℕ) ≤ cofinite →
      (∀ (a b : BoundedMatrixSequence (fun n ↦ X n)),
          normMatrixCStarCoronaMk (fun n ↦ X n) a
              = normMatrixCStarCoronaMk (fun n ↦ X n) b →
            TracialUltraproduct.seqUltratrace X ω a
              = TracialUltraproduct.seqUltratrace X ω b) ∧
      (∀ (a b : BoundedMatrixSequence (fun n ↦ X n)) (c : ℂ),
          TracialUltraproduct.seqUltratrace X ω (c • a + b)
            = c * TracialUltraproduct.seqUltratrace X ω a
              + TracialUltraproduct.seqUltratrace X ω b) ∧
      TracialUltraproduct.seqUltratrace X ω 1 = 1 ∧
      (∀ a : BoundedMatrixSequence (fun n ↦ X n),
          ∃ t : ℝ, 0 ≤ t ∧
            TracialUltraproduct.seqUltratrace X ω (star a * a) = (t : ℂ)) ∧
      (∀ a b : BoundedMatrixSequence (fun n ↦ X n),
          TracialUltraproduct.seqUltratrace X ω (a * b)
            = TracialUltraproduct.seqUltratrace X ω (b * a))

/-- **`thm:normal-kazhdan`, proof sentence, tex lines 670-673, closed.**  The
printed `τ`, exactly as printed: a well defined tracial state on `𝒬_r`. -/
theorem manuscriptSentence_ultrafilterNormalizedTraceIsWellDefinedTracialState :
    UltrafilterNormalizedTraceIsWellDefinedTracialState := by
  intro X _ ω hω
  refine ⟨fun a b h ↦ ?_, ?_, ?_, ?_, ?_⟩
  · exact manuscriptSentence_ultrafilterNormalizedTraceWellDefined X ω hω h
  · intro a b c
    rw [TracialUltraproduct.seqUltratrace_add X ω (c • a) b,
      TracialUltraproduct.seqUltratrace_smul X ω c a]
  · exact TracialUltraproduct.seqUltratrace_one X ω
  · intro a
    exact ⟨TracialUltraproduct.seqHSLimit X ω a,
      TracialUltraproduct.seqHSLimit_nonneg X ω a,
      TracialUltraproduct.seqUltratrace_star_mul_self X ω a⟩
  · intro a b
    exact TracialUltraproduct.seqUltratrace_mul_comm X ω a b

/-! ## `thm:normal-kazhdan`, proof sentences following the `τ` sentence

"The hypothesis applies to `(W_n)` itself, so `|tr_{r_n}(W_n(k)) - 1| ≤
‖W_n(k) - I_{r_n}‖₂ → 0` for `k ∈ K`, ..., and therefore `τ(π(u_k)) = 1` for
every `k ∈ K`, where `u_k` is the canonical unitary of `k`.  The trivial
character `χ` of `K` is the state of `C*_max(K)` with `χ(u_k) = 1` for every
`k`, and it has `χ(e_K) = 1`." -/

/-- **`thm:normal-kazhdan`, proof sentence: `τ(π(u_k)) = 1`.**  `τ(π(u_k))`
unfolds to `lim_ω tr_{r_n}(W_n(k))`, the ultrafilter limit of the normalized
traces of the corner representation `W = D.cornerMap` at `k`.  The theorem's
own Hilbert--Schmidt hypothesis, applied to `W` exactly as printed
(`NormalKazhdanPrintedRoute.manuscriptSentence_traceOfCombinationTendsTo`'s
first conjunct), already gives ordinary `atTop` convergence to `1`; freeness
of `ω` transports that to every free ultrafilter, so the ultrafilter limit is
`1` too. -/
theorem manuscriptSentence_ultrafilterTraceOfCornerUnitaryIsOne
    {G : Type} [Group G] {L : Type} [Group L] (iota : L →* G)
    (hres : ∀ s : L, iota s ∈ opToHSShadowResidual G)
    {model : ℕ → FiniteModel}
    (D : PrintedCornerCompression.PrintedCornerData G model)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) (s : L) :
    UltrafilterLimit.ulim ω (fun k ↦ normTrace (D.cornerModel k)
        ((D.cornerMap k (iota s) :
          Matrix (D.cornerModel k) (D.cornerModel k) ℂ)))
      = 1 := by
  have hωAtTop : (ω : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact hω
  exact UltrafilterLimit.ulim_eq
    (((OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptSentence_traceOfCombinationTendsTo
        iota hres D ∅ (fun _ ↦ 0)).1 s).mono_left hωAtTop)

/-- **`thm:normal-kazhdan`, proof sentence: the trivial character `χ`.**
`χ := maximalGroupCStarTrivialCharacter K`; both printed clauses are already
established simp lemmas of that construction — `χ(u_k) = 1` for every `k`,
and `χ(e_K) = 1`. -/
theorem manuscriptSentence_trivialCharacterProperties
    {K : Type} [Group K]
    (KD : MaximalCStarKazhdanProjection.KazhdanData K) :
    (∀ k : K, OneSidedMFRadical.maximalGroupCStarTrivialCharacter K
        (maximalGroupCStarGenerator K k) = 1) ∧
      OneSidedMFRadical.maximalGroupCStarTrivialCharacter K KD.projection
        = 1 :=
  ⟨OneSidedMFRadical.maximalGroupCStarTrivialCharacter_generator K,
    OneSidedMFRadical.maximalGroupCStarTrivialCharacter_kazhdanProjection KD⟩

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_ultrafilterNormalizedTraceIsWellDefinedTracialState
