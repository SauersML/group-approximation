import GroupApproximation.Analysis.ShulmanFillNormingConjugationLift
import GroupApproximation.Analysis.ShulmanFillNormingDoubledFlip
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftDouble
import GroupApproximation.Analysis.UniversalCStarAmalgam

/-!
# The flip does not separate the two legs of a doubled lift

`Analysis/ShulmanFillNormingExistentialLiftDouble` doubles one asymptotic lift
`φ` of `π` into an asymptotic lift `double φ` of `diag(π, π)` at the doubled
models, and `Analysis/ShulmanFillNormingDoubledFlip` exhibits the flip
`((0,1),(1,0))` as a unitary of the doubled `𝒟`.  The plan recorded in the
header of `Analysis/ShulmanFillNormingDoubleMF` was to obtain the second leg of
Shulman's Theorem 10 from the first by conjugating with that flip, so that
Theorem 10 would consume only *one* lift.

**That plan does not close, and the obstruction is exact rather than
quantitative.**  The flip commutes with every diagonal `diag(a, a)`, so it
commutes with every value of `double φ` — not merely on the image of `C`, which
is what Theorem 10 needs, but on all of `D`.  Conjugation therefore returns
`double φ` unchanged:

* `doubledFlipSeq_commute_doubledDiagSeq` — the flip commutes with every doubled
  diagonal sequence, coordinatewise by
  `ShulmanFill.flip2_commutes_diagonal2_self`;
* `conjugate_double_toFun` — hence `conjugate` fixes `double φ` term by term;
* `doubledRep_conjugate_eq` — and at the level of representations, the second
  leg `Ad (q U) ∘ diag(π, π)` *is* `diag(π, π)`.

The pair `(ρ₁, ρ₂)` that `StarStrongAsymptoticLift.isMFAlgebra_amalgam_of_glue`
would then receive is the constant pair, and its `hΛ` hypothesis — faithfulness
of the glued limit representation on `D *_C D` — collapses the double:
`universalCStarAmalgamLeft_eq_right_of_injective` shows that a compatible
representation whose two legs agree cannot be faithful unless the two canonical
maps `D → D *_C D` are equal.  Composing it with `doubledRep_conjugate_eq` at
`ρ₁ = ρ₂ = doubledRep π` is the counter-model: for any `k : C →⋆ₐ[ℂ] D` that is
not already an isomorphism onto `D`, the single-lift route cannot supply `hΛ`.

## What the paper does instead, and what is therefore still owed

Shulman's `ρ₁ = π₁ ⊕ π₂` and `ρ₂ = π₂ ⊕ π₁` are built from the *two* legs
`π₁ = π ∘ ι₁`, `π₂ = π ∘ ι₂` of a faithful representation `π` of the double, not
from one representation twice; the flip then genuinely swaps them.  Doubling one
lift can only produce `π ⊕ π`.  What is owed is therefore a lift of
`ρ₂ = π₂ ⊕ π₁` — a single representation of `D` — into a model *of the doubled
shape* `M₂(A n)`, i.e. Theorem 4 with the model constrained to be a matrix
amplification, or else the Halmos dilation of Shulman's Lemma 9, which lifts the
flip only approximately and pays for it with the commutator estimate.  Neither
is in the repository, and neither follows from
`Theorem4RepresentationFirstStatement`, which chooses the model itself.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## The flip fixes the doubled data -/

section Flip

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **The flip commutes with every doubled diagonal sequence.**  Coordinatewise
this is `ShulmanFill.flip2_commutes_diagonal2_self`: the flip commutes with a
two-by-two diagonal whose entries agree. -/
theorem doubledFlipSeq_commute_doubledDiagSeq
    (x : StarStrong.BoundedStarSequence A) :
    doubledFlipSeq (A := A) * doubledDiagSeq (A := A) x
      = doubledDiagSeq (A := A) x * doubledFlipSeq := by
  apply lp.ext
  funext n
  show (flip2 : DoubledModel A n) * cStarDiagonal2 (x n) (x n)
    = cStarDiagonal2 (x n) (x n) * flip2
  exact flip2_commutes_diagonal2_self (x n)

/-- **Conjugating a doubled lift by the flip changes nothing.**  Every value of
`double φ` is a doubled diagonal, and the flip commutes with all of them, so
`conjugate_toFun_eq_of_commute` applies at every `t` and every `b` — not only on
the image of the amalgamated algebra. -/
theorem conjugate_double_toFun
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    {B : Type} [CStarAlgebra B] {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (t : ℕ) (b : B) :
    (StarStrongAsymptoticLift.conjugate (doubledFlipSeq (A := A))
        (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
        (doubledFlipSeq_mul_star_self (A := A))
        (norm_doubledFlipSeq_le_one (A := A))
        (StarStrongAsymptoticLift.double ι φ)).toFun t b
      = (StarStrongAsymptoticLift.double ι φ).toFun t b :=
  StarStrongAsymptoticLift.conjugate_toFun_eq_of_commute
    (doubledFlipSeq (A := A)) (doubledFlipSeq_mem ι hone)
    (doubledFlipSeq_star_mul_self (A := A))
    (doubledFlipSeq_mul_star_self (A := A))
    (norm_doubledFlipSeq_le_one (A := A))
    (StarStrongAsymptoticLift.double ι φ) t b
    (doubledFlipSeq_commute_doubledDiagSeq (φ.toFun t b))

/-! ## The flip's limit, and the conjugated representation -/

/-- **The `*`-strong limit of the constant flip sequence is the flip of
`B(H ⊕ H)`.**  This is the witness that
`Analysis/ShulmanFillNormingDoubledFlip.doubledFlipSeq_mem` produces, named so
that `q` can be evaluated on it. -/
theorem isStarStrongLimit_doubledFlipSeq
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    StarStrong.IsStarStrongLimit
      (fun n ↦ doubledIota ι n ((doubledFlipSeq (A := A)) n))
      (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))) := by
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · have key : Tendsto (fun n ↦ hBlockOp ((CStarMatrix.mapₙₐ (ι n))
        (flip2 : DoubledModel A n)) v) atTop
        (𝓝 (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) v)) :=
      tendsto_hBlockOp_of_coord (tendsto_flip_entry ι hone) v
    exact key
  · have hstarL : ∀ n : ℕ,
        star (doubledIota ι n ((doubledFlipSeq (A := A)) n))
          = doubledIota ι n ((doubledFlipSeq (A := A)) n) := by
      intro n
      have h : star (doubledIota ι n (flip2 : DoubledModel A n))
          = doubledIota ι n (flip2 : DoubledModel A n) := by
        rw [← map_star, star_flip2]
      exact h
    have hstarR :
        star (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)))
          = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) := by
      rw [← hBlockOp_star, star_flip2]
    simp only [hstarL, hstarR]
    have key : Tendsto (fun n ↦ hBlockOp ((CStarMatrix.mapₙₐ (ι n))
        (flip2 : DoubledModel A n)) v) atTop
        (𝓝 (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) v)) :=
      tendsto_hBlockOp_of_coord (tendsto_flip_entry ι hone) v
    exact key

/-- The conjugating unitary of `B(H ⊕ H)` that the doubled flip supplies is the
flip of `B(H ⊕ H)`. -/
theorem limitUnitary_doubledFlipSeq
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    limitUnitary (doubledFlipSeq (A := A)) (doubledFlipSeq_mem ι hone)
      = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :=
  StarStrong.starStrongLimit_eq (doubledIota ι) (doubled_norm_le ι)
    (doubled_hone ι hone) ⟨doubledFlipSeq, doubledFlipSeq_mem ι hone⟩
    (isStarStrongLimit_doubledFlipSeq ι hone)

/-- **Conjugation by the flip is the identity on the doubled representation.**
`u diag(a, a) u* = diag(a, a)` is `ShulmanFill.flip2_conj_diagonal2` at equal
entries, pushed through the block homomorphism. -/
theorem unitaryConj_limitUnitaryBundled_doubledRep
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    {B : Type} [CStarAlgebra B] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : B) :
    unitaryConj (D := BlockSpace H 2 →L[ℂ] BlockSpace H 2)
        (limitUnitaryBundled (doubledFlipSeq (A := A))
          (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
          (doubledFlipSeq_mul_star_self (A := A)))
        (doubledRep π b) = doubledRep π b := by
  have hu : ((limitUnitaryBundled (doubledFlipSeq (A := A))
        (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
        (doubledFlipSeq_mul_star_self (A := A)) :
          unitary (BlockSpace H 2 →L[ℂ] BlockSpace H 2)) :
        BlockSpace H 2 →L[ℂ] BlockSpace H 2)
      = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :=
    limitUnitary_doubledFlipSeq ι hone
  have hstar :
      star (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)))
        = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) := by
    rw [← hBlockOp_star, star_flip2]
  rw [unitaryConj_apply, hu, doubledRep_apply, hstar, ← hBlockOp_mul,
    ← hBlockOp_mul]
  congr 1
  show (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
      * cStarDiagonal2 (π b) (π b) * flip2 = cStarDiagonal2 (π b) (π b)
  rw [flip2_conj_diagonal2]

/-- **The second leg is the first leg.**  Conjugating the doubled
representation by the flip returns it unchanged, so the pair that Theorem 10
would receive from a single doubled lift is the constant pair. -/
theorem doubledRep_conjugate_eq
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    {B : Type} [CStarAlgebra B] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (unitaryConj (D := BlockSpace H 2 →L[ℂ] BlockSpace H 2)
        (limitUnitaryBundled (doubledFlipSeq (A := A))
          (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
          (doubledFlipSeq_mul_star_self (A := A)))).comp (doubledRep π)
      = doubledRep π := by
  apply StarAlgHom.ext
  intro b
  exact unitaryConj_limitUnitaryBundled_doubledRep ι hone π b

end Flip

/-! ## Why a constant pair cannot be faithful on the double -/

section Collapse

variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D] (k : C →⋆ₐ[ℂ] D)
variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **A compatible representation of the symmetric double whose two legs agree
cannot be faithful unless the double collapses.**  The evaluation carries the
two canonical maps to the two legs, so if the legs agree and the evaluation is
injective, the two canonical maps `D → D *_C D` are equal. -/
theorem universalCStarAmalgamLeft_eq_right_of_injective
    (R : CStarAmalgamRepresentation k k) (hLR : ∀ d : D, R.left d = R.right d)
    (hinj : Function.Injective (universalCStarAmalgamEval k k R)) (d : D) :
    universalCStarAmalgamLeft k k d = universalCStarAmalgamRight k k d := by
  apply hinj
  rw [universalCStarAmalgamEval_left, universalCStarAmalgamEval_right]
  exact hLR d

/-- **The same, in the shape `StarStrongAsymptoticLift.limitRep` produces it.**
`limitRep k hρ` is `ofCompatiblePair k k ρ₁ ρ₂ hρ`, so a pair of equal legs
makes the faithfulness hypothesis `hΛ` of
`StarStrongAsymptoticLift.isMFAlgebra_amalgam_of_glue` collapse the amalgam.
With `ρ₁ = doubledRep π` and `ρ₂` its flip conjugate, `doubledRep_conjugate_eq`
supplies `hEq`, and this is the counter-model to the single-lift bridge. -/
theorem universalCStarAmalgamLeft_eq_right_of_injective_pair
    {E : Type} [CStarAlgebra E] [Nontrivial E] {ρ₁ ρ₂ : D →⋆ₐ[ℂ] E}
    (hρ : ρ₁.comp k = ρ₂.comp k) (hEq : ρ₁ = ρ₂)
    (hinj : Function.Injective (universalCStarAmalgamEval k k
      (CStarAmalgamRepresentation.ofCompatiblePair k k ρ₁ ρ₂ hρ)))
    (d : D) :
    universalCStarAmalgamLeft k k d = universalCStarAmalgamRight k k d :=
  universalCStarAmalgamLeft_eq_right_of_injective k
    (CStarAmalgamRepresentation.ofCompatiblePair k k ρ₁ ρ₂ hρ)
    (fun d' ↦ by
      show ρ₁ d' = ρ₂ d'
      exact DFunLike.congr_fun hEq d')
    hinj d

end Collapse

end

end ShulmanFill
end GroupApproximation
