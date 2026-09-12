import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:transport`, the displayed equivalence of the proof

`non_mf_groups_exist.tex`, proof of Theorem `thm:transport` (tex lines 511-515
at 73c867c5b):

> A Hilbert--Schmidt bounded sequence `(x_n)` lies in `𝒞₂(V,L)` if and only if
> `‖P_n x_n − x_n‖₂ → 0`.

The census graded this sentence `structural`, as a frame for the two
directions that follow.  It is a mathematical assertion in its own right, so it
gets its own closed carrier: the two directional lemmas of
`Manuscript/OneSidedMFRadical/TransportProjectionCharacterization.lean` combined
into the printed `if and only if`, for every lift `(P_n)` of the image `P` of
the Kazhdan projection of `L` under the homomorphism induced by `σ̃|_L`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportCharacterizationIffSentence

open Filter Matrix
open MaximalCStarKazhdanProjection
open HilbertSchmidtAdMatrix HilbertSchmidtOperatorAction TransportSigmaTilde
open TransportKazhdanProjection TransportProjectionCommutation
open TransportPrintedCommutant TransportProjectionCharacterization
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **`thm:transport`, proof sentence (tex lines 511-515).**

> A Hilbert--Schmidt bounded sequence `(x_n)` lies in `𝒞₂(V,L)` if and only if
> `‖P_n x_n − x_n‖₂ → 0`.

Here `V = B` is the operator norm asymptotic representation, `σ̃ = sigmaB B`
is the corona homomorphism `g ↦ [Ad(V_n(g))]_n`, `f` is the homomorphism
`C*_max(L) → 𝓑` induced by `σ̃|_L`, `P = f(e_L)`, and `(P_n)` is any bounded
lift of `P`.  The forward direction is
`TransportProjectionCharacterization.tendsto_hsNorm_applyOp_projection_sub`,
the reverse direction is
`TransportProjectionCharacterization.isHSAsymptoticallyCentral_of_tendsto`. -/
def PrintedCTwoIffProjectionAbsorbs : Prop :=
  ∀ (G : Type) [Group G] (B : OpAlmostRepresentation G)
    [∀ n, Nonempty (B.model n)] (L : Subgroup G) (KD : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
    (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n))),
    (∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B)) →
    normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq = f KD.projection →
    ∀ x : ∀ n, Matrix (B.model n) (B.model n) ℂ, IsHSBounded B x →
      (x ∈ printedCTwo B L ↔
        Tendsto (fun n ↦ hsNorm (B.model n)
          (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n))
          atTop (nhds 0))

theorem manuscriptSentence_printedCTwoIffProjectionAbsorbs :
    PrintedCTwoIffProjectionAbsorbs := by
  intro G _ B _ L KD f Pseq hf hPmk x hx
  constructor
  · intro hmem
    exact tendsto_hsNorm_applyOp_projection_sub B L KD f Pseq hf hPmk x hmem
  · intro h
    obtain ⟨C, hC⟩ := hx
    exact ⟨⟨C, hC⟩,
      isHSAsymptoticallyCentral_of_tendsto B L KD f Pseq hf hPmk x hC h⟩

end

end TransportCharacterizationIffSentence
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.TransportCharacterizationIffSentence.manuscriptSentence_printedCTwoIffProjectionAbsorbs
