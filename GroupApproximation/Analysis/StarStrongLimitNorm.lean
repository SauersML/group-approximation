import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ReducedProductMFPermanence
import GroupApproximation.Analysis.StarStrongMatrixSequencesAlgebra

/-!
# The faithfulness inequality of the `𝒟`-limit, and what it buys

`Analysis/StarStrongMatrixSequencesAlgebra` builds Shulman's algebra `𝒟` of
bounded sequences whose images converge `*`-strongly, and the limit map
`q : 𝒟 → B(H)`.  It proves that `q` kills the *norm-null* sequences.  This
module proves the inequality that statement is the `c = 0` case of:

    `‖q x‖ ≤ c` whenever `‖xₙ‖ ≤ c` for infinitely many `n`,

that is `‖q x‖ ≤ liminf ‖xₙ‖`.  The proof is one line of analysis —
`‖q x v‖` is the limit of `‖ι n (xₙ) v‖`, and along the frequent set that
sequence stays at or below `c ‖v‖`, so no gap `‖q x v‖ - c ‖v‖ > 0` can be
maintained — and it is the only property of `𝒟` that Shulman's criterion
consumes on the side the recognition lane needs.

## What it buys: the useful half of Theorem 4

With it, a `*`-homomorphism `ρ : B → 𝒟` whose composite with `q` is faithful
makes `B` embed in the *reduced product* `∏ₙ Aₙ / ⨁ₙ Aₙ`: if the corona class
of `ρ b` vanishes then `‖(ρ b)ₙ‖ → 0`, so `q (ρ b) = 0`, so `b = 0`.  When each
`Aₙ` is MF — matrix algebras, in the printed setting —
`Analysis/ReducedProductMFPermanence` then makes `B` itself MF.  That is
`isMFAlgebra_of_starStrongLift` below, and it is the direction of Shulman's
Theorem 4 that his Theorem 10 ends with.

The other direction — from `B` MF to the existence of a lift with faithful
`*`-strong limit — is *not* here, and it is the one Theorem 10 begins with.

## A correction: `MFLiftingCharacterization` is false as stated

`Analysis/StarStrongMatrixSequencesShulman` records Shulman's Theorem 4 as

    `∀ (ι : ∀ n, M n →⋆ₙₐ[ℂ] B(H)) (hnorm) (hone) (A), IsMFAlgebra A ↔ …`

quantified over an *arbitrary* family `M : ℕ → Type` of C-star algebras.  That
biconditional is refuted by the family itself, with no analysis: take `H := ℂ`
and `M n := ℂ`, with `ι n` the canonical map `ℂ → (ℂ →L[ℂ] ℂ)`, which is
contractive and unital, so `hnorm` and `hone` hold.  A C-star algebra with no
injective `*`-homomorphism into `ℂ` — any noncommutative one, or any
nonseparable commutative one such as `lp (fun _ : ℕ ↦ ℂ) ∞` — then satisfies
the right-hand side vacuously, and the nonseparable one is not MF, because
`IsMFAlgebra` contains separability.  So the `←` direction of the recorded
statement fails at that instance.  The same objection applies to
`MFContractiveLiftingCharacterization`.

The repair is not to weaken the biconditional but to name the models: what
Theorem 4 is about is `M n = M_{k_n}`, and the content the recognition lane
uses is the implication, at models that are themselves MF.  That implication is
`isMFAlgebra_of_starStrongLift` below, proved here with no hypothesis on the
family beyond `HasMFEmbedding (A n)`, which the matrix models satisfy.  Nothing
in this module cites the refuted biconditional.

This module is deliberately not in the root import list: it was authored while
builds were suspended, so it is kept out of the closure until it has been
elaborated, like the `Analysis/StarStrong*` modules it extends.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-! ## The faithfulness inequality -/

/-- **`‖q x‖ ≤ liminf ‖xₙ‖`.**  A bound holding for infinitely many
coordinates bounds the `*`-strong limit: for each vector `v` the sequence
`‖ι n (xₙ) v‖` converges to `‖q x v‖`, and it returns infinitely often to
`c ‖v‖` or below, so it cannot converge to anything larger. -/
theorem norm_starStrongLimit_le_of_frequently
    (x : starStrongSubalgebra ι hnorm hone) {c : ℝ} (hc : 0 ≤ c)
    (hfreq : ∃ᶠ n in atTop, ‖(x : BoundedStarSequence A) n‖ ≤ c) :
    ‖starStrongLimit ι hnorm hone x‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v ↦ ?_
  have hlim : Tendsto (fun n ↦ ‖ι n ((x : BoundedStarSequence A) n) v‖) atTop
      (𝓝 ‖starStrongLimit ι hnorm hone x v‖) :=
    ((starStrongLimit_spec ι hnorm hone x).1 v).norm
  have hcoord : ∀ n : ℕ, ‖(x : BoundedStarSequence A) n‖ ≤ c →
      ‖ι n ((x : BoundedStarSequence A) n) v‖ ≤ c * ‖v‖ := by
    intro n hn
    have h1 : ‖ι n ((x : BoundedStarSequence A) n) v‖ ≤
        ‖ι n ((x : BoundedStarSequence A) n)‖ * ‖v‖ :=
      (ι n ((x : BoundedStarSequence A) n)).le_opNorm v
    have h2 : ‖ι n ((x : BoundedStarSequence A) n)‖ ≤ c :=
      (hnorm n ((x : BoundedStarSequence A) n)).trans hn
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg v))
  by_contra hcon
  push_neg at hcon
  set L : ℝ := ‖starStrongLimit ι hnorm hone x v‖
  have hgap : 0 < L - c * ‖v‖ := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (L - c * ‖v‖) hgap
  obtain ⟨n, hfn, hnN⟩ :=
    (hfreq.and_eventually (eventually_ge_atTop N)).exists
  have hd := hN n hnN
  rw [Real.dist_eq, abs_lt] at hd
  have hle := hcoord n hfn
  linarith [hd.1]

/-- The eventual form of the same bound. -/
theorem norm_starStrongLimit_le_of_eventually
    (x : starStrongSubalgebra ι hnorm hone) {c : ℝ} (hc : 0 ≤ c)
    (hev : ∀ᶠ n in atTop, ‖(x : BoundedStarSequence A) n‖ ≤ c) :
    ‖starStrongLimit ι hnorm hone x‖ ≤ c :=
  norm_starStrongLimit_le_of_frequently ι hnorm hone x hc hev.frequently

/-- **`q` is contractive**, the `ℓ∞`-bound being available at every
coordinate. -/
theorem norm_starStrongLimit_le (x : starStrongSubalgebra ι hnorm hone) :
    ‖starStrongLimit ι hnorm hone x‖ ≤ ‖(x : BoundedStarSequence A)‖ :=
  norm_starStrongLimit_le_of_eventually ι hnorm hone x (norm_nonneg _)
    (Eventually.of_forall fun n ↦
      lp.norm_apply_le_norm ENNReal.top_ne_zero (x : BoundedStarSequence A) n)

/-! ## `𝒟` over the reduced product -/

variable [∀ n, Nontrivial (A n)]

/-- `𝒟` sits inside the bounded product, so it maps to the reduced product
`∏ₙ Aₙ / ⨁ₙ Aₙ`. -/
def coronaOfStarStrong :
    starStrongSubalgebra ι hnorm hone →⋆ₐ[ℂ] CStarProductCorona A cofinite :=
  (cStarProductCoronaQuotient A cofinite).comp
    (starStrongSubalgebra ι hnorm hone).subtype

@[simp] theorem coronaOfStarStrong_apply
    (x : starStrongSubalgebra ι hnorm hone) :
    coronaOfStarStrong ι hnorm hone x =
      cStarProductCoronaQuotient A cofinite (x : BoundedStarSequence A) :=
  rfl

/-- **The reduced-product evaluation of a `𝒟`-lift is faithful as soon as its
`*`-strong limit is.**  A class killed by the reduced product is a norm-null
sequence, and `q` kills those. -/
theorem coronaOfStarStrong_comp_injective
    {B : Type v} [CStarAlgebra B]
    (rho : B →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone)
    (hfaithful :
      Function.Injective fun b : B ↦ starStrongLimitHom ι hnorm hone (rho b)) :
    Function.Injective fun b : B ↦ coronaOfStarStrong ι hnorm hone (rho b) := by
  intro b₁ b₂ hb
  have hb' : coronaOfStarStrong ι hnorm hone (rho b₁) =
      coronaOfStarStrong ι hnorm hone (rho b₂) := hb
  have hzero : coronaOfStarStrong ι hnorm hone (rho (b₁ - b₂)) = 0 := by
    rw [map_sub, map_sub, hb', sub_self]
  have hzero' : cStarProductCoronaQuotient A cofinite
      ((rho (b₁ - b₂) : starStrongSubalgebra ι hnorm hone) :
        BoundedStarSequence A) = 0 := hzero
  have hnull : IsNullCStarSequence A cofinite
      ((rho (b₁ - b₂) : starStrongSubalgebra ι hnorm hone) :
        BoundedStarSequence A) :=
    (cStarProductCoronaQuotient_eq_zero_iff A cofinite _).mp hzero'
  have htend : Tendsto
      (fun n ↦ ‖((rho (b₁ - b₂) : starStrongSubalgebra ι hnorm hone) :
        BoundedStarSequence A) n‖) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hnull
  have hq : starStrongLimit ι hnorm hone (rho (b₁ - b₂)) = 0 :=
    starStrongLimit_eq_zero_of_tendsto_norm_zero ι hnorm hone _ htend
  have hsub : b₁ - b₂ = 0 := by
    apply hfaithful
    show starStrongLimitHom ι hnorm hone (rho (b₁ - b₂)) =
      starStrongLimitHom ι hnorm hone (rho 0)
    rw [map_zero, map_zero]
    exact hq
  exact eq_of_sub_eq_zero hsub

/-- **The half of Shulman's Theorem 4 that the recognition lane consumes.**  A
separable algebra with a `*`-homomorphic lift into `𝒟` whose `*`-strong limit
is faithful is MF, as soon as the coordinate algebras are.

No hypothesis on the family beyond `HasMFEmbedding (A n)` is needed; the
printed case is `A n = M_{k_n}`, where that is automatic. -/
theorem isMFAlgebra_of_starStrongLift
    (hA : ∀ n, HasMFEmbedding (A n))
    {B : Type v} [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
    (rho : B →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone)
    (hfaithful :
      Function.Injective fun b : B ↦ starStrongLimitHom ι hnorm hone (rho b)) :
    IsMFAlgebra B :=
  ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct A
    ((coronaOfStarStrong ι hnorm hone).comp rho).toNonUnitalStarAlgHom
    (coronaOfStarStrong_comp_injective ι hnorm hone rho hfaithful) hA

end

end StarStrong
end GroupApproximation
