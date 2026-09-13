import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedForms
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceNormalizedAlmostRepresentationClosure
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem `thm:normal-kazhdan` with its hypothesis at the printed generality

`non_mf_groups_exist.tex`, Theorem `thm:normal-kazhdan` (tex lines 658–662):

> Let `G` be countable and let `K ⊴ G` have property (T).  If every operator norm
> asymptotic representation `(V_n)` of `G` satisfies `‖V_n(k) − 1‖₂ → 0` for all
> `k ∈ K`, then every corona homomorphism from `G` is trivial on `K`.

The manuscript defines an operator norm asymptotic representation at tex lines
410–414 as a sequence of maps `V_n : G → U(d_n)` such that `V_n(1) = 1` and
`‖V_n(gh) − V_n(g)V_n(h)‖ → 0`; that is `PrintedOpAlmostRepresentation`.
`PrintedNormalKazhdan` ranges its hypothesis over every `OpAlmostRepresentation`,
which does not require `V_n(1) = 1`, so as a hypothesis it assumes more than the
printed one.  This file states the theorem with the hypothesis over the printed
normalized sequences only.  The two hypotheses are equivalent: normalizing at the
identity changes no value off the identity, and at the identity
`‖V_n(1) − 1‖₂ ≤ ‖V_n(1) − 1‖ → 0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix
open scoped Matrix.Norms.L2Operator
open OneSidedMFRadical

/-- The Hilbert--Schmidt displacement condition passes back through normalization
at the identity: off the identity the normalized maps are unchanged, and at the
identity `‖A_n(1) − 1‖₂ ≤ ‖A_n(1) − 1‖ → 0`. -/
theorem hsVanishes_of_normalized {G : Type} [Group G]
    (A : OpAlmostRepresentation G) (k : G)
    (h : HSVanishes (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation k) :
    HSVanishes A k := by
  by_cases hk : k = 1
  · subst hk
    have hop : Tendsto
        (fun n ↦ ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖)
        atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ :=
        KazhdanCornerMatrices.map_one_vanishing A (ε / 2) (half_pos hε)
      refine ⟨N, fun n hn ↦ ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact (hN n hn).trans_lt (half_lt_self hε)
    change Tendsto
      (fun n ↦ hsNorm (A.model n)
        ((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1))
      atTop (nhds 0)
    exact squeeze_zero (fun n ↦ hsNorm_nonneg _ _)
      (fun n ↦ PrelimNotation.hsNorm_le_l2_opNorm _ _) hop
  · change Tendsto
      (fun n ↦ Real.sqrt (hsLengthSq (A.model n)
        ((normalizedOpMap A n k : Matrix (A.model n) (A.model n) ℂ))))
      atTop (nhds 0) at h
    show Tendsto
      (fun n ↦ Real.sqrt (hsLengthSq (A.model n)
        ((A.map n k : Matrix (A.model n) (A.model n) ℂ))))
      atTop (nhds 0)
    exact Filter.Tendsto.congr
      (fun n ↦ by rw [normalizedOpMap_of_ne_one A n hk]) h

/-- The hypothesis of `thm:normal-kazhdan` over the normalized sequences of tex
lines 410–414 is equivalent to the same hypothesis over every
`OpAlmostRepresentation`. -/
theorem normalizedHSHypothesis_iff {G : Type} [Group G] (K : Subgroup G) :
    (∀ V : PrintedOpAlmostRepresentation G, ∀ k ∈ K,
        HSVanishes V.toOpAlmostRepresentation k) ↔
      ∀ A : OpAlmostRepresentation G, ∀ k ∈ K, HSVanishes A k :=
  ⟨fun h A k hk ↦
      hsVanishes_of_normalized A k (h (opAlmostRepresentationToPrinted A) k hk),
    fun h V k hk ↦ h V.toOpAlmostRepresentation k hk⟩

/-- **Theorem `thm:normal-kazhdan` (tex lines 658–662), at the printed generality.**

> Let `G` be countable and let `K ⊴ G` have property (T).  If every operator norm
> asymptotic representation `(V_n)` of `G` satisfies `‖V_n(k) − 1‖₂ → 0` for all
> `k ∈ K`, then every corona homomorphism from `G` is trivial on `K`.

The hypothesis ranges over `PrintedOpAlmostRepresentation`, the sequences with
`V_n(1) = 1` (tex lines 410–414).  `‖x‖₂` is the normalized Hilbert--Schmidt norm
(`hsLengthSq` is `tr_d((u − 1)^*(u − 1))`), and a corona homomorphism is a
homomorphism into the unitary group of `∏ M_{d_n}(ℂ) / ⊕ M_{d_n}(ℂ)`
(`ManuscriptCoronaMFInvisible`). -/
def PrintedNormalKazhdanNormalizedHypothesis : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G) [K.Normal],
    HasKazhdanPropertyT.{0, 0} ↥K →
      (∀ V : PrintedOpAlmostRepresentation G, ∀ k ∈ K,
          HSVanishes V.toOpAlmostRepresentation k) →
        ∀ k ∈ K, ManuscriptCoronaMFInvisible k

theorem manuscriptPrintedNormalKazhdanNormalizedHypothesis :
    PrintedNormalKazhdanNormalizedHypothesis := by
  intro G _ _ K _ hT hV
  exact manuscriptPrintedNormalKazhdan G K hT ((normalizedHSHypothesis_iff K).mp hV)

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms
  Manuscript.NonMFSentences.hsVanishes_of_normalized
#audit_axioms
  Manuscript.NonMFSentences.normalizedHSHypothesis_iff
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptPrintedNormalKazhdanNormalizedHypothesis
