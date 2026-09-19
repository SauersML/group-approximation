import GroupApproximation.Analysis.ShulmanFillNormingGluing
import GroupApproximation.Analysis.ShulmanFillNormingTailGlueAlign

/-!
# Gluing two tail lifts over `C`

`Analysis/ShulmanFillNormingGluing` glues two asymptotic lifts of `D` agreeing
on `C` into one representation of `D *_C D`, and reads its faithfulness off the
limits.  This module does the same for `StarStrongTailLift`s.

The argument is the one it mirrors, with two substitutions.  `sHom` replaces
`dHom`, so the legs land in `∏_t 𝒟_{cut t} / ⨁_t` --- unital, because
relabelling is.  And the two legs are aligned first at `commonCut φ₁ φ₂`, since
`sHom` is indexed by the lift's own cut and the universal property needs both
legs in one algebra; `withCut` costs nothing, so no hypothesis relating the cuts
is needed.

The one place the vocabulary shows is the limit clause.  `dHom`'s legs satisfy
`q̂ ∘ Θᵢ = constCorona (ρᵢ)` because each `φ_t` lifts `ρᵢ` exactly; a tail lift
only converges, so the same identity holds because the difference is null in the
reduced product, which is what `tendsto_lift` says and all the faithfulness
argument ever needed.  `limitHom_sSeq` is what carries it across the
relabelling.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

section TailGluing

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The descent of the coordinate limits to the reduced products.  The data
`ι`, `hnorm`, `hone` are implicit here and explicit in
`Analysis/ShulmanFillNormingTailGlueAlign`'s `ShiftedD.limitHom`, so the cut is
this map's first and only explicit argument. -/
def tailLimitCoronaMap (c : ℕ → ℕ) :
    CStarProductCorona (fun t ↦ ShiftedD ι hnorm hone c t) cofinite →⋆ₐ[ℂ]
      CStarProductCorona (fun _ : ℕ ↦ (H →L[ℂ] H)) cofinite :=
  coronaMap (fun t ↦ ShiftedD.limitHom ι hnorm hone c t) cofinite

variable {k}

/-- **The limit of a tail lift is the constant sequence of the representation it
lifts.**  Not because each `φ_t` lifts it exactly --- it does not --- but
because the difference is null, which is `tendsto_lift`. -/
theorem tailLimitCoronaMap_sHom {B : Type} [CStarAlgebra B]
    {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (φ : StarStrongTailLift ι hnorm hone π) (b : B) :
    tailLimitCoronaMap φ.cut (sHom φ b)
      = constCorona (E := (H →L[ℂ] H)) cofinite (π b) := by
  rw [sHom_apply, sClass, tailLimitCoronaMap, coronaMap_mk]
  refine cStarProductCoronaQuotient_eq_of_tendsto_norm_sub _ _ ?_
  refine (φ.tendsto_lift b).congr fun t ↦ ?_
  rw [show (boundedMap (fun t ↦ ShiftedD.limitHom ι hnorm hone φ.cut t)
      (sSeq φ b)) t = ShiftedD.limitHom ι hnorm hone φ.cut t (sSeq φ b t) from rfl,
    limitHom_sSeq φ b t]
  rfl

variable (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
  (φ₂ : StarStrongTailLift ι hnorm hone ρ₂)

/-- The left leg, re-cut to the common cut. -/
abbrev alignLeft : StarStrongTailLift ι hnorm hone ρ₁ :=
  φ₁.withCut (commonCut φ₁ φ₂) (le_commonCut_left φ₁ φ₂)

/-- The right leg, re-cut to the common cut. -/
abbrev alignRight : StarStrongTailLift ι hnorm hone ρ₂ :=
  φ₂.withCut (commonCut φ₁ φ₂) (le_commonCut_right φ₁ φ₂)

variable (k)

omit [Nontrivial (H →L[ℂ] H)] in
/-- **Two legs agreeing on `C` past their cuts are a compatible pair.** -/
theorem sHom_comp_eq
    (hagree : ∀ c : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k c) - φ₂.toFun t (k c))) :
    (sHom (alignLeft φ₁ φ₂)).comp k = (sHom (alignRight φ₁ φ₂)).comp k := by
  refine StarAlgHom.ext fun c ↦ ?_
  show sClass (alignLeft φ₁ φ₂) (k c) = sClass (alignRight φ₁ φ₂) (k c)
  rw [sClass, sClass]
  exact sClass_eq_of_tailNull (alignLeft φ₁ φ₂)
    (fun t ↦ φ₁.toFun t (k c)) (fun t ↦ φ₂.toFun t (k c))
    (sSeq (alignLeft φ₁ φ₂) (k c)) (sSeq (alignRight φ₁ φ₂) (k c))
    (fun t ↦ val_sSeq_apply (alignLeft φ₁ φ₂) (k c) t)
    (fun t ↦ val_sSeq_apply (alignRight φ₁ φ₂) (k c) t) (hagree c)

/-- **Lemma 7 in the repaired vocabulary: the glued representation.** -/
def glueRepTail
    (hagree : ∀ c : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k c) - φ₂.toFun t (k c))) :
    CStarAmalgamRepresentation k k :=
  CStarAmalgamRepresentation.ofCompatiblePair k k
    (sHom (alignLeft φ₁ φ₂)) (sHom (alignRight φ₁ φ₂))
    (sHom_comp_eq k φ₁ φ₂ hagree)

variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **The limit map intertwines the glued evaluation with the constant
embedding of the limit evaluation.**  Both sides are `*`-homomorphisms out of
the amalgam agreeing on the two factor images, so the uniqueness half of the
universal property identifies them. -/
theorem tailLimitCoronaMap_comp_glue
    (hagree : ∀ c : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k c) - φ₂.toFun t (k c)))
    (hρ : ρ₁.comp k = ρ₂.comp k) (x : UniversalCStarAmalgam k k) :
    tailLimitCoronaMap (commonCut φ₁ φ₂)
        (universalCStarAmalgamEval k k (glueRepTail k φ₁ φ₂ hagree) x)
      = constCorona (E := (H →L[ℂ] H)) cofinite
        (universalCStarAmalgamEval k k
          (StarStrongAsymptoticLift.limitRep k hρ) x) := by
  have hcompat :
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₁).comp k =
        ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₂).comp k := by
    refine StarAlgHom.ext fun c ↦ ?_
    exact congrArg (constCorona (E := (H →L[ℂ] H)) cofinite)
      (DFunLike.congr_fun hρ c)
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift k k
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₁)
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₂) hcompat
  have hleft := huniq
    ((tailLimitCoronaMap (commonCut φ₁ φ₂)).comp
      (universalCStarAmalgamEval k k (glueRepTail k φ₁ φ₂ hagree)))
    ⟨fun d ↦ tailLimitCoronaMap_sHom (alignLeft φ₁ φ₂) d,
      fun d ↦ tailLimitCoronaMap_sHom (alignRight φ₁ φ₂) d⟩
  have hright := huniq
    ((constCorona (E := (H →L[ℂ] H)) cofinite).comp
      (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ)))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) x

/-- **Faithfulness of the glued map.**  It transfers from the pair of limits,
exactly as in the sup-norm vocabulary: the limit map carries the glued
evaluation to the constant embedding of the limit evaluation, and the constant
embedding is faithful. -/
theorem injective_glueRepTail_eval
    (hagree : ∀ c : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k c) - φ₂.toFun t (k c)))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k hρ))) :
    Function.Injective
      (universalCStarAmalgamEval k k (glueRepTail k φ₁ φ₂ hagree)) := by
  intro x y hxy
  apply hΛ
  apply constCorona_injective (E := (H →L[ℂ] H)) cofinite
  rw [← tailLimitCoronaMap_comp_glue k φ₁ φ₂ hagree hρ x,
    ← tailLimitCoronaMap_comp_glue k φ₁ φ₂ hagree hρ y, hxy]

end TailGluing

end

end ShulmanFill
end GroupApproximation
