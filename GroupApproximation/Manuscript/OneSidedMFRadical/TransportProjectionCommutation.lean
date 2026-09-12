import GroupApproximation.Manuscript.OneSidedMFRadical.TransportKazhdanProjection
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness
import GroupApproximation.Analysis.CollapseProjectionLift

/-!
# `[U, P] = 0` for the printed `thm:transport`

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`:

> Put `U = σ̃(u)`.  Since `uLu⁻¹ ≤ L`, `U σ̃(L) U* ⊆ σ̃(L)`, so `U*PU ≤ P` by
> Lemma `lem:kazhdan-projection-order`, and `U*PU = P` by Lemma
> `lem:stable-finite`, since the two projections are unitarily equivalent.
> So `[U, P] = 0`.

The two lemmas the sentence cites are in the corpus:
`Analysis/MaximalCStarKazhdanProjection.lean` proves the one-sided order in
the absorption form the argument uses, and
`Manuscript/OneSidedMFRadical/StableFiniteness.lean` proves
`lem:stable-finite` with its projection-comparison consequence.  This module
puts `U = σ̃(u)` into them.

The order relation is taken in the conjugated form `P ≤ U P U*` rather than
the printed `U*PU ≤ P`; the two are the same statement conjugated by `U`, and
`conj_image_mul_image` states the first directly, so no order structure has to
be installed on the corona to say it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportProjectionCommutation

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open HilbertSchmidtAdMatrix TransportSigmaTilde
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] (B : OpAlmostRepresentation G)
  [∀ n, Nonempty (B.model n)]

/-- **The printed corona `𝓑 = ∏_n B(M_{d_n}(ℂ)) / ⊕_n B(M_{d_n}(ℂ))`**, read
as a norm matrix corona with coordinate sizes `d_n²`. -/
abbrev sqCorona : Type := NormMatrixCStarCorona (fun n ↦ sqModel (B.model n))

omit [∀ n, Nonempty (B.model n)] in
/-- The multiplicative defect of an operator norm asymptotic representation
vanishes, in the `Tendsto` form the corona construction consumes. -/
theorem tendsto_mul_defect (g h : G) :
    Tendsto (fun n ↦ ‖(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ)
      - (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
        (B.map n h : Matrix (B.model n) (B.model n) ℂ)‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative g h (eps / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith [hN n hn]

/-- **`σ̃`, for an operator norm asymptotic representation.** -/
def sigmaB : G →* unitary (sqCorona B) :=
  sigmaTilde B.model B.map (fun g h ↦ tendsto_mul_defect B g h)

theorem sigmaB_coe (g : G) :
    ((sigmaB B g : unitary (sqCorona B)) : sqCorona B)
      = normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n))
          (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
            (adUnitary B.model B.map g)) := rfl

/-! ## The Kazhdan projection and its lift -/

/-- **"Let `P ∈ 𝓑` be the image of the Kazhdan projection of `L` under
`C*_max(L) → 𝓑`, and lift `P` to orthogonal projections `P_n` … by functional
calculus."** -/
theorem exists_projectionData (L : Subgroup G) (KD : KazhdanData ↥L) :
    ∃ (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
      (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n))),
      (∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
        = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B)) ∧
      (∀ n, IsOrthogonalProjectionMatrix
        ((Pseq : ∀ n, Matrix (sqModel (B.model n)) (sqModel (B.model n)) ℂ)
          n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
        = f KD.projection := by
  obtain ⟨f, hf, -⟩ := maximalGroupCStar_existsUnique_lift_allUniverses ↥L
    ((sigmaB B).comp L.subtype)
  obtain ⟨Pseq, hPproj, hPmk⟩ :=
    CollapseProjectionLift.exists_projection_lift
      (fun n ↦ sqModel (B.model n)) (f KD.projection)
      (isSelfAdjoint_image KD f) (image_mul_image KD f)
  exact ⟨f, Pseq, hf, hPproj, hPmk⟩

/-! ## The commutation -/

/-- **`[U, P] = 0`.**

`uLu⁻¹ ≤ L` gives `U σ̃(L) U* ⊆ σ̃(L)`, which is the compression hypothesis of
`lem:kazhdan-projection-order`; that lemma's absorption form
(`conj_image_mul_image`) is `P ≤ U P U*`, the printed `U*PU ≤ P` conjugated by
`U`.  The two projections are unitarily equivalent, so `lem:stable-finite`'s
comparison clause turns the domination into an equality, and the commutation
follows by one line of unitarity. -/
theorem commute_sigmaB_projection (L : Subgroup G) (KD : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    {u : G} (hu : u ∈ compressionSet L) :
    ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection
      = f KD.projection * ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) := by
  have hU : star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
      ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) = 1 :=
    Unitary.star_mul_self_of_mem (sigmaB B u).2
  have hU' : ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
      star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) = 1 :=
    Unitary.mul_star_self_of_mem (sigmaB B u).2
  have hcomp : ∀ s : ↥L, ∃ t : ↥L,
      ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
          (((sigmaB B).comp L.subtype s : unitary (sqCorona B)) : sqCorona B) *
          star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
        = (((sigmaB B).comp L.subtype t : unitary (sqCorona B)) :
            sqCorona B) := by
    refine compresses_coe ((sigmaB B).comp L.subtype) (sigmaB B u) ?_
    intro s
    refine ⟨⟨u * (s : G) * u⁻¹, hu (s : G) s.2⟩, ?_⟩
    show sigmaB B u * sigmaB B (s : G) * (sigmaB B u)⁻¹
      = sigmaB B (u * (s : G) * u⁻¹)
    rw [map_mul, map_mul, map_inv]
  have h1 := conj_image_mul_image KD ((sigmaB B).comp L.subtype) f hf
    ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) hU hU' hcomp
  have hsp : IsStarProjection (f KD.projection) := isStarProjection_image KD f
  have hspq : IsStarProjection
      (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection *
        star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) := by
    constructor
    · show (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
            f KD.projection *
            star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) *
          (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
            f KD.projection *
            star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B))
        = ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
            f KD.projection *
            star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
      have hstep : (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
              f KD.projection *
              star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) *
            (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
              f KD.projection *
              star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B))
          = ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
              (f KD.projection *
                (star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
                  ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) *
                f KD.projection) *
              star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) := by
        noncomm_ring
      rw [hstep, hU, mul_one]
      exact congrArg (fun z ↦
        ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * z *
          star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B))
        (image_mul_image KD f)
    · exact isSelfAdjoint_conj_image KD f
        ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
  obtain ⟨-, hstable⟩ :=
    manuscriptNormMatrixCoronaStableFinite (fun n ↦ sqModel (B.model n))
  have heq : f KD.projection
      = ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection *
        star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) :=
    hstable (f KD.projection)
      (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection *
        star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B))
      ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) hsp hspq hU rfl h1
  calc ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection
      = ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection *
          (star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
            ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) := by
        rw [hU, mul_one]
    _ = (((sigmaB B u : unitary (sqCorona B)) : sqCorona B) * f KD.projection *
          star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)) *
        ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) := by noncomm_ring
    _ = f KD.projection *
        ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) := by rw [← heq]

end

end TransportProjectionCommutation
end OneSidedMFRadical
end Manuscript
end GroupApproximation
