import GroupApproximation.Analysis.ShulmanFillNormingDoubleMF
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLift
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftPair

/-!
# Theorem 4 for the two legs of a double, and Theorem 10 wired to it

`Analysis/ShulmanFillNormingExistentialLift` states Theorem 4's lifting
direction with the model chosen after *one* representation.  That is not what
Shulman's Theorem 10 consumes.  Theorem 10 starts from a faithful `π` of the
double `D *_C D` and uses its two legs `ρ₁ = π ∘ ι₁`, `ρ₂ = π ∘ ι₂`, which have
to be lifted into the **same** `𝒟` — the flip that swaps them lives in one
sequence algebra, not in two.  `Theorem4TwoLegStatement` below is that binder:
the model is chosen after *both* representations.

Its consumer is `isMFAlgebra_amalgam_of_doubleLR`, which is
`StarStrongAsymptoticLift.isMFAlgebra_amalgam_of_glue` rewired through
`Analysis/ShulmanFillNormingExistentialLiftPair`:

* `doubleLR φ₁ φ₂` lifts `pairRep ρ₁ ρ₂` into the doubled `𝒟`;
* `doubleLR φ₂ φ₁` lifts `pairRep ρ₂ ρ₁`, and it is not a second assumption —
  `conjugate_doubleLR_toFun` shows it *is* the flip conjugate of the first,
  term by term, and `pairRep_conjugate_eq` says the same of the two limits;
* the two agree on `C` because `‖diag(u - v, v - u)‖ = ‖u - v‖`, so the
  agreement hypothesis is the one `φ₁` and `φ₂` already carry on `H`;
* compatibility of the pair, `hρ`, is inherited by `pairRep_comp_eq`.

So exactly **one** lift of the doubled representation is ever assumed, and the
inputs of Theorem 10 are now: two lifts on `H` into one `𝒟`, their asymptotic
agreement on `C`, MF-ness of the doubled `𝒟`, and faithfulness of the glued
limit.  The last two were already binders of `isMFAlgebra_amalgam_of_glue` and
are unchanged.

## The status of `Theorem4TwoLegStatement`

It is an open named `Prop`, and it is **too weak to be the lane's input**: it
lacks the agreement clause on `C` that `isMFAlgebra_amalgam_of_doubleLR`
consumes, so it cannot drive Theorem 10.  `ShulmanFill.Theorem4PrintedPairStatement`
of `Analysis/ShulmanFillNormingExistentialLiftPrinted` supersedes it, and with
`ShulmanSymmetricDouble.CompatibleTargetPairStatement` that one is the analytic
input the recognition route cites rather than proves.

Nothing here is deleted, because this statement is the record of where the
weaker forms sit: `theorem4RepresentationFirst_of_twoLeg` shows it implies the
one-leg form of `Analysis/ShulmanFillNormingExistentialLift`, which in turn is
implied by the refuted model-first form.  The chain of strengths is

    `Theorem4ModelFirstStatement`  (FALSE, `not_theorem4ModelFirst`)
      ⟹ `Theorem4TwoLegStatement`  ⟹ `Theorem4RepresentationFirstStatement` ,

with `Theorem4PrintedPairStatement` off to the side of it — stronger than the
two-leg form in the agreement clause, and narrower in the coefficients.

## What a prescribed-model form would buy, and why it is not stated here

If Theorem 4 could be asked with the model *prescribed* up to a matrix
amplification — a lift of a single `ρ : D → B(H ⊕ H)` into `M₂(A n)` for a given
`(A, ι)` — then one lift would suffice, since the flip is already a unitary of
the doubled `𝒟`.  That is what Shulman's Lemma 9 buys with a Halmos dilation:
the flip is lifted only approximately, to `V = ((X̃, √(1 - X̃X̃*)),
(√(1 - X̃*X̃), -X̃*))`, and Pedersen's commutator inequality pays for the error.
Such a form quantifies the model before the representation and is therefore in
the danger zone of `Analysis/ShulmanFillNormingTheorem4Refuted`; it is recorded
here in prose only, and not as a binder.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## The two-leg binder -/

/-- **Shulman's Theorem 4, lifting direction, for a pair of representations.**
For every separable Hilbert space `H`, every separable MF algebra `B` and every
pair of faithful representations `ρ₁, ρ₂ : B →⋆ₐ[ℂ] B(H)` there is *one* family
of C-star algebras `A n` with MF coefficients and *one* contractive family of
embeddings `ι n : A n → B(H)` with `ι n (1) → 1` strongly, carrying discrete
asymptotic homomorphisms of `B` lifting `ρ₁` and `ρ₂` through the `*`-strong
limit map.

The single model is the whole point: the flip that exchanges the two legs of a
symmetric double is a unitary of one sequence algebra, so the two lifts have to
live in the same one.

**Too weak, and superseded.**  This binder produces two lifts into one model and
says nothing relating them on `C`, whereas
`ShulmanFill.isMFAlgebra_amalgam_of_doubleLR` needs
`∀ c, ‖φ₁_t (k c) - φ₂_t (k c)‖ → 0` — Shulman's Lemma 9, the clause the Halmos
dilation and Pedersen's commutator inequality are for in the paper.  It is part
of the same package as Theorem 4 and Remark 6, not something a consumer can be
asked to supply, so this statement cannot drive Theorem 10.
`ShulmanFill.Theorem4PrintedPairStatement` of
`Analysis/ShulmanFillNormingExistentialLiftPrinted` is the repair: it carries
the agreement clause, and by pinning the coefficients to the printed family it
also makes the `hD` hypothesis of Theorem 10 a theorem rather than an
assumption.  Nothing below is deleted, because
`theorem4RepresentationFirst_of_twoLeg` is the record of where this form sits in
the chain of strengths.

The model-first form, in which `A` and `ι` are quantified before `B`, `ρ₁` and
`ρ₂`, is `Theorem4ModelFirstStatement` and is refuted by
`not_theorem4ModelFirst`. -/
def Theorem4TwoLegStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (B : Type) [CStarAlgebra B] [TopologicalSpace.SeparableSpace B],
      IsMFAlgebra B →
      ∀ ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H),
        Function.Injective ρ₁ → Function.Injective ρ₂ →
        ∃ (A : ℕ → Type) (hcstar : ∀ n, CStarAlgebra (A n)),
          letI : ∀ n, CStarAlgebra (A n) := hcstar
          ∃ hnontrivial : ∀ n, Nontrivial (A n),
            letI : ∀ n, Nontrivial (A n) := hnontrivial
            ∃ (_ : ∀ n, HasMFEmbedding (A n))
              (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
              (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
              (hone : ∀ v : H,
                Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)),
              Nonempty (StarStrongAsymptoticLift ι hnorm hone ρ₁) ∧
                Nonempty (StarStrongAsymptoticLift ι hnorm hone ρ₂)

/-- **The two-leg form implies the one-leg form.**  Take both legs to be the
same representation and keep the first lift. -/
theorem theorem4RepresentationFirst_of_twoLeg
    (h : Theorem4TwoLegStatement) :
    Theorem4RepresentationFirstStatement := by
  intro H _ _ _ _ B _ _ hB π hπ
  obtain ⟨A, hcstar, hnontrivial, hMF, ι, hnorm, hone, hlift, _⟩ :=
    h B hB π π hπ hπ
  exact ⟨A, hcstar, hnontrivial, hMF, ι, hnorm, hone, hlift⟩

/-! ## Compatibility of the paired representations -/

section Compatibility

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The paired representations inherit compatibility.**  On the image of `C`
the two legs agree, so both `diag(ρ₁, ρ₂)` and `diag(ρ₂, ρ₁)` are the same
diagonal there. -/
theorem pairRep_comp_eq {C B : Type} [CStarAlgebra C] [CStarAlgebra B]
    (k : C →⋆ₐ[ℂ] B) {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ₁.comp k = ρ₂.comp k) :
    (pairRep ρ₁ ρ₂).comp k = (pairRep ρ₂ ρ₁).comp k := by
  apply StarAlgHom.ext
  intro c
  have h : ρ₁ (k c) = ρ₂ (k c) := DFunLike.congr_fun hρ c
  show pairRep ρ₁ ρ₂ (k c) = pairRep ρ₂ ρ₁ (k c)
  rw [pairRep_apply, pairRep_apply, h]

end Compatibility

/-! ## Theorem 10, rewired -/

section Rewiring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

omit [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
  [TopologicalSpace.SeparableSpace D]
  [Nonempty (CStarAmalgamRepresentation k k)] in
/-- **The two doubled legs agree on `C`.**  Their difference is
`diag(u - v, v - u)`, whose norm is `max ‖u - v‖ ‖v - u‖ = ‖u - v‖`, so the
agreement of the two lifts on `H` transfers unchanged. -/
theorem tendsto_norm_sub_doubleLR
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (c : C) :
    Tendsto (fun t ↦
      ‖(StarStrongAsymptoticLift.doubleLR ι φ₁ φ₂).toFun t (k c)
        - (StarStrongAsymptoticLift.doubleLR ι φ₂ φ₁).toFun t (k c)‖)
      atTop (𝓝 0) := by
  refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) (hagree c)
  have h : doubledPairSeq (A := A) (φ₁.toFun t (k c)) (φ₂.toFun t (k c))
        - doubledPairSeq (A := A) (φ₂.toFun t (k c)) (φ₁.toFun t (k c))
      = doubledPairSeq (A := A)
          (φ₁.toFun t (k c) - φ₂.toFun t (k c))
          (φ₂.toFun t (k c) - φ₁.toFun t (k c)) := by
    rw [doubledPairSeq_sub]
  show ‖doubledPairSeq (A := A) (φ₁.toFun t (k c)) (φ₂.toFun t (k c))
      - doubledPairSeq (A := A) (φ₂.toFun t (k c)) (φ₁.toFun t (k c))‖
    ≤ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖
  rw [h]
  refine (norm_doubledPairSeq_le _ _).trans (le_of_eq ?_)
  rw [norm_sub_rev (φ₂.toFun t (k c)) (φ₁.toFun t (k c)), max_self]

/-- **Shulman's Theorem 10 from a single doubled lift.**  Two asymptotic lifts
of `ρ₁` and `ρ₂` into one `𝒟` on `H` are doubled to a lift of `diag(ρ₁, ρ₂)`
into the doubled `𝒟`, and the flip supplies the second leg exactly
(`conjugate_doubleLR_toFun`), so no second lift of the doubled representation is
assumed.  The remaining hypotheses are those
`StarStrongAsymptoticLift.isMFAlgebra_amalgam_of_glue` already had: MF-ness of
the doubled `𝒟`, agreement on `C`, compatibility, and faithfulness of the pair
of limits. -/
theorem isMFAlgebra_amalgam_of_doubleLR
    (hD : HasMFEmbedding (StarStrong.starStrongSubalgebra (doubledIota ι)
      (doubled_norm_le ι) (doubled_hone ι hone)))
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k (pairRep_comp_eq k hρ)))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) :=
  StarStrongAsymptoticLift.isMFAlgebra_amalgam_of_glue k hD
    (StarStrongAsymptoticLift.doubleLR ι φ₁ φ₂)
    (StarStrongAsymptoticLift.doubleLR ι φ₂ φ₁)
    (tendsto_norm_sub_doubleLR ι hnorm hone k φ₁ φ₂ hagree)
    (pairRep_comp_eq k hρ) hΛ

end Rewiring

end

end ShulmanFill
end GroupApproximation
