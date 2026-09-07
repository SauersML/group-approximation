import GroupApproximation.Manuscript.OneSidedMFRadical.TransportSigmaTilde
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarTrivialCharacter

/-!
# The Kazhdan projection of `thm:transport`, and the printed `ε`-estimate

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`:

> Let `P ∈ 𝓑` be the image of the Kazhdan projection of `L` under
> `C*_max(L) → 𝓑`, and lift `P` to orthogonal projections `P_n` on
> `(M_{d_n}(ℂ), ‖·‖₂)` by functional calculus. … fix `ε > 0` and, by density
> of the group algebra in `C*_max(L)`, a finite set `F ⊆ L` and scalars
> `(a_ℓ)` with `‖Σ a_ℓ u_ℓ − e_L‖ < ε`; the trivial character gives
> `|Σ a_ℓ − 1| < ε`.  The element `Σ a_ℓ σ̃(ℓ)` of `𝓑` is within `ε` of `P`,
> so `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`.

This module carries those sentences: the projection and its lift exist, the
`ε`-form of the density-plus-character estimate, and the passage from the
corona to the coordinates.  The `1/4` instance of the same density estimate is
`NormalKazhdanPrintedRoute.manuscriptSentence_denseCombinationAndCharacter`,
used by the normal-Kazhdan proof; the transport proof needs it at an arbitrary
`ε`, which is the only difference.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportKazhdanProjection

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open HilbertSchmidtAdMatrix TransportSigmaTilde
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Density and the trivial character, at an arbitrary `ε` -/

/-- **`‖Σ a_ℓ u_ℓ − e_L‖ < ε` and `|Σ a_ℓ − 1| < ε`.**  The `ε`-form of the
density-plus-trivial-character estimate. -/
theorem exists_combination_close {L : Type} [Group L] (KD : KazhdanData L)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (F : Finset L) (alpha : L → ℂ),
      ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
          - KD.projection‖ < eps ∧
        ‖(∑ s ∈ F, alpha s) - 1‖ < eps := by
  obtain ⟨F, alpha, hclose⟩ :=
    NormalKazhdanPrintedRoute.exists_generatorCombination_close (K := L)
      KD.projection heps
  refine ⟨F, alpha, hclose, ?_⟩
  have hchi : maximalGroupCStarTrivialCharacter L
      ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s) - KD.projection)
      = (∑ s ∈ F, alpha s) - 1 := by
    rw [map_sub, maximalGroupCStarTrivialCharacter_kazhdanProjection KD, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, maximalGroupCStarTrivialCharacter_generator, smul_eq_mul,
      mul_one]
  rw [← hchi]
  exact lt_of_le_of_lt
    (NonUnitalStarAlgHom.norm_apply_le (maximalGroupCStarTrivialCharacter L) _)
    hclose

/-! ## The printed `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε` -/

section Coordinates

variable {G : Type} [Group G] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
  (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)
  (hmul : ∀ g h : G, Tendsto (fun n ↦
    ‖(V n (g * h) : Matrix (X n) (X n) ℂ)
      - (V n g : Matrix (X n) (X n) ℂ) * (V n h : Matrix (X n) (X n) ℂ)‖)
    atTop (nhds 0))
  (L : Subgroup G) (KD : KazhdanData ↥L)
  (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ]
    NormMatrixCStarCorona (fun n ↦ sqModel (X n)))
  (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (X n)))

/-- The bounded sequence of the printed `Ad(V_n(ℓ))`. -/
def adSeq (ell : ↥L) : BoundedMatrixSequence (fun n ↦ sqModel (X n)) :=
  unitarySequenceBounded (fun n ↦ sqModel (X n))
    (adUnitary X V (L.subtype ell))

@[simp] theorem adSeq_apply (ell : ↥L) (n : ℕ) :
    (adSeq X V L ell : ∀ n, Matrix (sqModel (X n)) (sqModel (X n)) ℂ) n
      = adMatrix (X n) (V n (L.subtype ell)) := rfl

theorem mk_adSeq (ell : ↥L) :
    normMatrixCStarCoronaMk (fun n ↦ sqModel (X n)) (adSeq X V L ell)
      = ((sigmaTilde X V hmul (L.subtype ell) :
          unitary (NormMatrixCStarCorona (fun n ↦ sqModel (X n)))) :
        NormMatrixCStarCorona (fun n ↦ sqModel (X n))) := rfl

/-- The printed finite combination, as a bounded matrix sequence. -/
def combSeq (F : Finset ↥L) (alpha : ↥L → ℂ) :
    BoundedMatrixSequence (fun n ↦ sqModel (X n)) :=
  ∑ s ∈ F, alpha s • adSeq X V L s

theorem combSeq_apply (F : Finset ↥L) (alpha : ↥L → ℂ) (n : ℕ) :
    (combSeq X V L F alpha :
        ∀ n, Matrix (sqModel (X n)) (sqModel (X n)) ℂ) n
      = ∑ s ∈ F, alpha s • adMatrix (X n) (V n (L.subtype s)) := by
  classical
  rw [combSeq]
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, lp.coeFn_zero, Pi.zero_apply]
  · intro b s hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, lp.coeFn_add, Pi.add_apply,
      ih, lp.coeFn_smul, Pi.smul_apply, adSeq_apply]

theorem mk_combSeq (F : Finset ↥L) (alpha : ↥L → ℂ)
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaTilde X V hmul (L.subtype s) :
          unitary (NormMatrixCStarCorona (fun n ↦ sqModel (X n)))) :
        NormMatrixCStarCorona (fun n ↦ sqModel (X n)))) :
    normMatrixCStarCoronaMk (fun n ↦ sqModel (X n)) (combSeq X V L F alpha)
      = f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator ↥L s) := by
  rw [combSeq]
  show normMatrixCStarCoronaQuotient (fun n ↦ sqModel (X n)) _ = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, map_smul, hf s]
  rfl

/-- **The printed `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`.**  The element
`Σ a_ℓ σ̃(ℓ)` of `𝓑` is `f` of the printed combination, `P` is `f(e_L)`, and a
`⋆`-homomorphism is contractive, so the corona distance is at most
`‖Σ a_ℓ u_ℓ − e_L‖`; the corona norm is the `limsup` of the coordinate
norms. -/
theorem limsup_norm_sub_combSeq_lt
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaTilde X V hmul (L.subtype s) :
          unitary (NormMatrixCStarCorona (fun n ↦ sqModel (X n)))) :
        NormMatrixCStarCorona (fun n ↦ sqModel (X n))))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (X n)) Pseq
      = f KD.projection)
    (F : Finset ↥L) (alpha : ↥L → ℂ) {eps : ℝ}
    (hclose : ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator ↥L s)
      - KD.projection‖ < eps) :
    Filter.limsup (fun n ↦
        ‖(Pseq : ∀ n, Matrix (sqModel (X n)) (sqModel (X n)) ℂ) n
          - ∑ s ∈ F, alpha s • adMatrix (X n) (V n (L.subtype s))‖)
      Filter.cofinite < eps := by
  have hsub := map_sub (normMatrixCStarCoronaMk (fun n ↦ sqModel (X n)))
    Pseq (combSeq X V L F alpha)
  have hval : normMatrixCStarCoronaMk (fun n ↦ sqModel (X n))
      (Pseq - combSeq X V L F alpha)
      = f (KD.projection
        - ∑ s ∈ F, alpha s • maximalGroupCStarGenerator ↥L s) := by
    rw [hsub, hPmk, mk_combSeq X V hmul L f F alpha hf, ← map_sub f]
  have hnorm : ‖normMatrixCStarCoronaMk (fun n ↦ sqModel (X n))
      (Pseq - combSeq X V L F alpha)‖ < eps := by
    rw [hval]
    refine lt_of_le_of_lt (NonUnitalStarAlgHom.norm_apply_le f _) ?_
    rw [norm_sub_rev]
    exact hclose
  rw [norm_normMatrixCStarCoronaMk_eq_limsup (fun n ↦ sqModel (X n))
    (Pseq - combSeq X V L F alpha)] at hnorm
  refine lt_of_le_of_lt (le_of_eq ?_) hnorm
  congr 1
  funext n
  congr 1
  rw [lp.coeFn_sub, Pi.sub_apply, combSeq_apply]

end Coordinates

end

end TransportKazhdanProjection
end OneSidedMFRadical
end Manuscript
end GroupApproximation
