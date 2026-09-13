import GroupApproximation.Manuscript.NonMFSentences.NormalKazhdanUltrafilterRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Meta.AxiomGuard

/-!
# The introduction's second step: the limiting trace is the trivial character

`non_mf_groups_exist.tex`, Introduction (tex line 187), the outline of the proof
of Theorem `thm:compression-criterion`:

> Second, let `K ≤ 𝔇_G(L)` be a normal property-(T) subgroup and let a corona
> homomorphism be nontrivial on `K`.  It compresses to a corner on which the
> Kazhdan projection of `K` vanishes, and the corner, renormalized by its own
> rank, carries an operator norm asymptotic representation to which the first
> step applies.  Its limiting trace is then the trivial character of `K`, which
> takes the value `1` on that projection (Theorem `thm:normal-kazhdan`).

The corner is a `PrintedCornerData` of `G`, with corner representation
`(W_n) = D.cornerMap` and corona homomorphism `cornerCoronaUnitaryHom D`; `π` is
the homomorphism `C*_max(K) → 𝒬_r` it induces on `K`, and the limiting trace is
`τ∘π`, where `τ` is the limit of the normalized traces of the corner coordinates
along a free ultrafilter.  "The first step applies": `K ≤ 𝔇_G(L)` lies in the
shadow residual by Corollary `cor:defect-hs`
(`printedDefect_le_opToHSShadowResidual_direct`), so `τ(π(u_k)) = 1` for every
`k ∈ K`, and `τ∘π` and `χ` agree on `C*_max(K)`.  The sentences of the proof of
`thm:normal-kazhdan` used here are in `NormalKazhdanUltrafilterRoute.lean`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open OneSidedMFRadical
open OneSidedMFRadical.NormalKazhdanPrintedRoute
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Introduction, second step (tex line 187).**

> Its limiting trace is then the trivial character of `K`, which takes the value
> `1` on that projection (Theorem `thm:normal-kazhdan`).

`G` countable, `L ≤ G` with property (T), `K ⊴ G` with property (T) and
`K ≤ 𝔇_G(L)`, `e_K = KD.projection`.  For every corner `D`, every free
ultrafilter `ω` and the homomorphism `π : C*_max(K) → 𝒬_r` induced by the corner's
corona homomorphism on `K`, the limiting trace `τ∘π` is the trivial character `χ`
of `K` on all of `C*_max(K)`, and `χ(e_K) = 1`. -/
def PrintedIntroLimitingTraceIsTrivialCharacter : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L →
          ∀ (KD : KazhdanData ↥K) (model : ℕ → FiniteModel)
            (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
            (hω : (ω : Filter ℕ) ≤ cofinite)
            (π : MaximalGroupCStar ↥K →⋆ₐ[ℂ]
              NormMatrixCStarCorona (fun n ↦ D.cornerModel n)),
            (∀ s : ↥K, π (maximalGroupCStarGenerator ↥K s)
              = ((cornerCoronaUnitaryHom D (K.subtype s) :
                  unitary (NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) :
                    NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) →
              (∀ x : MaximalGroupCStar ↥K,
                ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω (π x)
                  = maximalGroupCStarTrivialCharacter ↥K x) ∧
                maximalGroupCStarTrivialCharacter ↥K KD.projection = 1

theorem manuscriptPrintedIntroLimitingTraceIsTrivialCharacter :
    PrintedIntroLimitingTraceIsTrivialCharacter := by
  intro G _ _ L hL K _ _ hKD KD _ D ω hω π hπ
  have hτπ := manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne K.subtype
    (fun s ↦ printedDefect_le_opToHSShadowResidual_direct L hL (hKD s.2))
    D ω hω π hπ
  exact ⟨(manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra π
      (ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω) hτπ).2.2,
    (manuscriptSentence_trivialCharacterIsStateWithValues KD).2.2.2⟩

/-- **Introduction, second step, the cited theorem (tex line 187).**

> ... (Theorem `thm:normal-kazhdan`).

The two values contradict the vanishing of the Kazhdan projection on the corner,
so no corona homomorphism is nontrivial on `K`: along the printed ultrafilter
route (`manuscriptNormalKazhdanRadical_ultrafilterRoute`), `K` lies in the corona
MF residual. -/
def PrintedIntroSecondStepConclusion : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L → K ≤ actualCoronaMFResidual G

theorem manuscriptPrintedIntroSecondStepConclusion :
    PrintedIntroSecondStepConclusion := by
  intro G _ _ L hL K _ hT hKD
  exact manuscriptNormalKazhdanRadical_ultrafilterRoute G K hT
    (hKD.trans (printedDefect_le_opToHSShadowResidual_direct L hL))

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptPrintedIntroLimitingTraceIsTrivialCharacter
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptPrintedIntroSecondStepConclusion
