import GroupApproximation.Analysis.ShulmanFillNormingDoubleMF
import GroupApproximation.Analysis.ShulmanFillNormingTailGluing

/-!
# Theorem 10 from a doubled tail lift

`ShulmanFill.isMFAlgebra_amalgam_of_doubleLR` derives MF-ness of the symmetric
double from two asymptotic lifts of `ρ₁` and `ρ₂` into one `𝒟`.  This module is
the same derivation for `StarStrongTailLift`s, on top of the gluing of
`Analysis/ShulmanFillNormingTailGluing`.

Two things differ, and neither is a new idea.

* **The agreement transfers cut-agnostically.**  The doubled difference is the
  paired sequence of the difference and its negative, so at every coordinate its
  norm is the norm of the difference; `TailNull.mono` carries the hypothesis
  across whatever cut is in play, which is what lets the doubled legs be aligned
  afterwards rather than before.
* **The MF hypothesis is now a family.**  The coordinate algebras of the reduced
  product are `𝒟` of the data relabelled past the cut, one per stage, so
  `HasMFEmbedding` is asked of each rather than once.  At the printed models
  these are again `𝒟`s of matrix families, so the discharge is the same
  argument; that is the next module's business.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

section TailDoubleMF

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}

omit [Nontrivial (H →L[ℂ] H)] in
/-- **The agreement on `C` survives doubling**, at whatever cut it is stated.
The doubled difference is the paired sequence of the difference and its
negative, whose coordinate norms are those of the difference. -/
theorem tailNull_sub_doubleLR
    (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongTailLift ι hnorm hone ρ₂) (c : ℕ → ℕ) (x : C)
    (hagree : TailNull c (fun t ↦ φ₁.toFun t (k x) - φ₂.toFun t (k x))) :
    TailNull c (fun t ↦
      (StarStrongTailLift.doubleLR φ₁ φ₂).toFun t (k x)
        - (StarStrongTailLift.doubleLR φ₂ φ₁).toFun t (k x)) := by
  have hmono : ∀ {B : ℕ → Type} [∀ n, CStarAlgebra (B n)]
      (Y : ℕ → StarStrong.BoundedStarSequence B),
      (∀ t n, ‖(Y t : ∀ n, B n) n‖
          ≤ ‖((fun t ↦ φ₁.toFun t (k x) - φ₂.toFun t (k x)) t
              : ∀ n, A n) n‖) →
      TailNull c Y := by
    intro B _ Y h ε hε
    exact (hagree ε hε).mono fun t ht n hn ↦ (h t n).trans (ht n hn)
  refine hmono (fun t ↦
    (StarStrongTailLift.doubleLR φ₁ φ₂).toFun t (k x)
      - (StarStrongTailLift.doubleLR φ₂ φ₁).toFun t (k x)) ?_
  intro t n
  have hsub : doubledPairSeq (A := A) (φ₁.toFun t (k x)) (φ₂.toFun t (k x))
        - doubledPairSeq (A := A) (φ₂.toFun t (k x)) (φ₁.toFun t (k x))
      = doubledPairSeq (A := A)
          (φ₁.toFun t (k x) - φ₂.toFun t (k x))
          (φ₂.toFun t (k x) - φ₁.toFun t (k x)) := by
    rw [doubledPairSeq_sub]
  show ‖(doubledPairSeq (A := A) (φ₁.toFun t (k x)) (φ₂.toFun t (k x))
      - doubledPairSeq (A := A) (φ₂.toFun t (k x)) (φ₁.toFun t (k x))) n‖
    ≤ ‖(φ₁.toFun t (k x) - φ₂.toFun t (k x)) n‖
  rw [hsub, doubledPairSeq_apply]
  refine (norm_diagonalPairHom2_le _).trans (le_of_eq ?_)
  show max ‖(φ₁.toFun t (k x) - φ₂.toFun t (k x)) n‖
      ‖(φ₂.toFun t (k x) - φ₁.toFun t (k x)) n‖
    = ‖(φ₁.toFun t (k x) - φ₂.toFun t (k x)) n‖
  rw [show ((φ₂.toFun t (k x) - φ₁.toFun t (k x)) : _) n
      = -((φ₁.toFun t (k x) - φ₂.toFun t (k x)) n) from by
    rw [← neg_sub (φ₁.toFun t (k x)) (φ₂.toFun t (k x)), lp.coeFn_neg]
    rfl, norm_neg, max_self]

variable [Nonempty (CStarAmalgamRepresentation k k)]
-- The permanence step needs the double separable, which it reads off `D`; the
-- unshifted `Analysis/ShulmanFillNormingDoubleMF` carries the same binder.  It
-- is declared here rather than with the section so that `tailNull_sub_doubleLR`,
-- which does not use it, does not carry it either.
variable [TopologicalSpace.SeparableSpace D]

omit [∀ (n : ℕ), StarOrderedRing (A n)] in
omit [(n : ℕ) → PartialOrder (A n)] in
/-- **Theorem 10's conclusion from a glued tail lift.**  The coordinate algebras
of the reduced product vary with the stage, so MF-ness is asked of each. -/
theorem isMFAlgebra_amalgam_of_tailGlue
    (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongTailLift ι hnorm hone ρ₂)
    (hD : ∀ t, HasMFEmbedding (ShiftedD ι hnorm hone (commonCut φ₁ φ₂) t))
    (hagree : ∀ x : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k x) - φ₂.toFun t (k x)))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) := by
  haveI : TopologicalSpace.SeparableSpace (UniversalCStarAmalgam k k) :=
    separableSpace_universalCStarAmalgam k k
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    (fun t ↦ ShiftedD ι hnorm hone (commonCut φ₁ φ₂) t)
    (universalCStarAmalgamEval k k
      (glueRepTail k φ₁ φ₂ hagree)).toNonUnitalStarAlgHom
    (injective_glueRepTail_eval k φ₁ φ₂ hagree hρ hΛ) hD

end TailDoubleMF

end

end ShulmanFill
end GroupApproximation
