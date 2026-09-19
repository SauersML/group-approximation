import GroupApproximation.Analysis.ShulmanCoronaNontrivial
import GroupApproximation.Analysis.ShulmanFillNormingCoronaMap
import GroupApproximation.Analysis.ShulmanFillNormingSeqHom
import GroupApproximation.Analysis.UniversalCStarAmalgam

/-!
# Gluing two asymptotic lifts over `C`, and why the glued map is faithful

Shulman's Lemma 7 glues two asymptotic homomorphisms of `D` that agree
asymptotically on `C` into one on `D *_C D`, through a contractive section of
`C_b(Λ, D) → C_b(Λ, D)/C_0(Λ, D)`.  In the vocabulary of
`Analysis/ShulmanFillNormingAsymptotic` no section is needed, and no `ε/3`
argument either.

The reason is `Analysis/ShulmanFillNormingSeqHom`: an asymptotic lift is an
honest **unital** `*`-homomorphism `Θ = dHom φ` into the reduced product
`∏_t 𝒟 / ⨁_t 𝒟`.  Two of them agreeing on `C` are a compatible pair, so the
*universal property of the amalgam* glues them — that is `glueRep` below, and
it is the whole of Lemma 7 here.

Faithfulness is the same trick once more.  The `*`-strong limit map
`q : 𝒟 → B(H)` acts coordinatewise on sequences, so by
`Analysis/ShulmanFillNormingCoronaMap` it descends to
`q̂ : ∏_t 𝒟 / ⨁_t 𝒟 → ∏_t B(H) / ⨁_t B(H)`, and because each `φ_t` lifts its
representation *exactly*, `q̂ ∘ Θ_i` is the **constant** embedding of `ρ_i`.
So `q̂ ∘ Ψ` and `ĉ ∘ Λ` are two homomorphisms out of the amalgam agreeing on
both factor images, hence equal, and since `ĉ` is faithful the faithfulness of
`Λ = ρ₁ * ρ₂` transfers to `Ψ` at once.  No word induction, no density.

That last hypothesis is what Shulman's Theorem 10 supplies by symmetry: with
`π = π₁ * π₂` faithful on the double, `ρ₁ = π₁ ⊕ π₂` and `ρ₂ = π₂ ⊕ π₁` have
`ρ₁ * ρ₂ = π ⊕ (π ∘ flip)`, which is faithful; and the two legs agree on `C`
*exactly* because the flip commutes with `diag(x, x)`
(`Analysis/ShulmanFillNormingConjugationLift.conjugate_toFun_eq_of_commute`).

## What is still owed above this

`IsMFAlgebra (D *_C D)` needs the coordinate algebras of the target reduced
product to be MF, that is `HasMFEmbedding 𝒟`, which reduces to
`HasMFEmbedding (∏ₙ A n)` since `𝒟` is a subalgebra of the bounded product.
That is an elementary block-sum construction and is not in the repository.
The alternative is to weaken the `lift` field to an asymptotic one, as the
docstring of `Analysis/ShulmanFillNormingAsymptotic` describes, and route the
conclusion through `isMFAlgebra_of_asymptoticLift` instead.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

section Gluing

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace StarStrongAsymptoticLift

/-- The descent of the `*`-strong limit map to the reduced products. -/
abbrev limitCoronaMap :
    DCorona ι hnorm hone →⋆ₐ[ℂ]
      CStarProductCorona (fun _ : ℕ ↦ (H →L[ℂ] H)) cofinite :=
  coronaMap (fun _ : ℕ ↦ StarStrong.starStrongLimitHom ι hnorm hone) cofinite

/-- **The limit of a lift is the constant sequence of the representation it
lifts.**  Each `φ_t` lifts `π` exactly, so the sequence `t ↦ q (φ_t d)` is
constant at `π d`. -/
theorem limitCoronaMap_dHom {B : Type} [CStarAlgebra B]
    {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (b : B) :
    limitCoronaMap (dHom φ b)
      = constCorona (E := (H →L[ℂ] H)) cofinite (π b) := by
  show limitCoronaMap
      (cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite (dSeq φ b)) =
    cStarProductCoronaQuotient (fun _ : ℕ ↦ (H →L[ℂ] H)) cofinite
      (constSeq (π b))
  rw [coronaMap_mk]
  congr 1
  apply lp.ext
  funext t
  exact φ.lift t b

variable (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
  (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)

omit [Nontrivial (H →L[ℂ] H)] in
/-- **Two legs agreeing asymptotically on `C` are a compatible pair.**  This is
the hypothesis of Shulman's Lemma 7 verbatim: the agreement need only hold in
the limit, because a null difference is invisible in the reduced product.
Exact agreement, which the flip supplies, is the special case
`dHom_comp_eq_of_eq`. -/
theorem dHom_comp_eq
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0)) :
    (dHom φ₁).comp k = (dHom φ₂).comp k := by
  apply StarAlgHom.ext
  intro c
  exact dClass_eq_of_tendsto (fun t ↦ φ₁.toFun t (k c))
    (fun t ↦ φ₂.toFun t (k c)) (dSeq φ₁ (k c)) (dSeq φ₂ (k c))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (hagree c)

omit [Nontrivial (H →L[ℂ] H)] in
/-- Exact agreement on `C` is asymptotic agreement.  This is the form the flip
produces, through
`Analysis/ShulmanFillNormingConjugationLift.conjugate_toFun_eq_of_commute`. -/
theorem tendsto_norm_sub_of_eq
    (hagree : ∀ (t : ℕ) (c : C), φ₁.toFun t (k c) = φ₂.toFun t (k c)) (c : C) :
    Tendsto (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0) := by
  have hfun : (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) =
      fun _ : ℕ ↦ (0 : ℝ) := by
    funext t
    rw [hagree t c, sub_self, norm_zero]
  rw [hfun]
  exact tendsto_const_nhds

/-- **Lemma 7 here: the glued representation of the amalgam.**  The universal
property of `D *_C D` needs nothing beyond the compatibility of the pair. -/
def glueRep
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0)) :
    CStarAmalgamRepresentation k k :=
  CStarAmalgamRepresentation.ofCompatiblePair k k (dHom φ₁) (dHom φ₂)
    (dHom_comp_eq k φ₁ φ₂ hagree)

/-- The representation of the amalgam carried by the two limits. -/
def limitRep (hρ : ρ₁.comp k = ρ₂.comp k) : CStarAmalgamRepresentation k k :=
  CStarAmalgamRepresentation.ofCompatiblePair k k ρ₁ ρ₂ hρ

variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **The limit map intertwines the glued evaluation with the constant
embedding of the limit evaluation.**  Both sides are `*`-homomorphisms out of
the amalgam taking the same values on the two factor images, so the uniqueness
half of the universal property identifies them. -/
theorem limitCoronaMap_comp_glue
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (x : UniversalCStarAmalgam k k) :
    limitCoronaMap (universalCStarAmalgamEval k k (glueRep k φ₁ φ₂ hagree) x) =
      constCorona (E := (H →L[ℂ] H)) cofinite
        (universalCStarAmalgamEval k k (limitRep k hρ) x) := by
  have hcompat :
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₁).comp k =
        ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₂).comp k := by
    apply StarAlgHom.ext
    intro c
    exact congrArg (constCorona (E := (H →L[ℂ] H)) cofinite)
      (DFunLike.congr_fun hρ c)
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift k k
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₁)
      ((constCorona (E := (H →L[ℂ] H)) cofinite).comp ρ₂) hcompat
  have hleft := huniq
    (limitCoronaMap.comp
      (universalCStarAmalgamEval k k (glueRep k φ₁ φ₂ hagree)))
    ⟨fun d ↦ limitCoronaMap_dHom φ₁ d, fun d ↦ limitCoronaMap_dHom φ₂ d⟩
  have hright := huniq
    ((constCorona (E := (H →L[ℂ] H)) cofinite).comp
      (universalCStarAmalgamEval k k (limitRep k hρ)))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) x

/-- **Faithfulness of the glued map.**  It transfers from the pair of limits,
because the limit map carries the glued evaluation to the constant embedding of
the limit evaluation, and the constant embedding is faithful. -/
theorem injective_glueRep_eval
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k (limitRep k hρ))) :
    Function.Injective
      (universalCStarAmalgamEval k k (glueRep k φ₁ φ₂ hagree)) := by
  intro x y hxy
  apply hΛ
  apply constCorona_injective (E := (H →L[ℂ] H)) cofinite
  rw [← limitCoronaMap_comp_glue k φ₁ φ₂ hagree hρ x,
    ← limitCoronaMap_comp_glue k φ₁ φ₂ hagree hρ y, hxy]

end StarStrongAsymptoticLift

end Gluing

end

end ShulmanFill
end GroupApproximation
