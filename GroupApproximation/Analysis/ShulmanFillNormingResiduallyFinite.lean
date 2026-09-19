import GroupApproximation.Analysis.StarStrongMatrixSequencesShulman

/-!
# A `*`-homomorphic `𝒟`-lift makes its source residually `(A n)`

`StarStrong.MFOfStarStrongLiftStatement` of
`Analysis/StarStrongMatrixSequencesShulman` reads Shulman's Theorem 4 with an
honest `*`-homomorphism `ρ : B →⋆ₐ[ℂ] 𝒟` as the lift, and
`StarStrong.mfOfStarStrongLift` proves the implication that Theorem 10 *ends*
with.  The direction Theorem 10 *begins* with — from `B` MF to the existence of
such a `ρ` with faithful `*`-strong limit — is the lane's next target.  This
module shows that in this reading it is **false**, and says what the repair is.

## The obstruction

`𝒟 = starStrongSubalgebra ι hnorm hone` is a star subalgebra of the *bounded
product* `∏ₙ A n`.  So coordinate evaluation `∏ₙ A n → A n` is a unital
`*`-homomorphism (`boundedStarSequenceCoord`), and composing it with a lift
gives, for each `n`, a genuine representation `B → A n`
(`starStrongCoord`).  If the `*`-strong limit of the lift is faithful, those
representations *separate the points of `B`*: a `b` killed by all of them has
`ρ b = 0` coordinatewise, hence norm-null coordinates, hence `q (ρ b) = 0`,
hence `b = 0`.  That is
`exists_nonzero_starStrongCoord_of_ne_zero` and `eq_of_forall_starStrongCoord_eq`
below, and `eq_zero_of_forall_hom_to_model_eq_zero` is the contrapositive: a
`B` admitting no nonzero representation in any `A n` admits no faithful lift
unless it is zero.

## Why that refutes the lifting direction at the printed family

The printed family is `A n = M_{kₙ}`, so "separated by the coordinate
representations" is exactly *residual finite dimensionality*.  MF does not
imply RFD, and the standard witness is the one Shulman's own paper leans on:
`C*_r(F_2)` is MF (Haagerup--Thorbjørnsen), separable, simple and
infinite-dimensional, so it has **no nonzero finite-dimensional representation
whatsoever**.  By `eq_zero_of_forall_hom_to_model_eq_zero` it therefore has no
`*`-homomorphic `𝒟`-lift with faithful `*`-strong limit, while it does have a
faithful representation.  So

> MF `⟹` there is a `*`-homomorphism `ρ : B → 𝒟` with `q ∘ ρ` faithful

is false, and no amount of work will discharge it.

## What is *not* refuted, and what the repair is

* `StarStrong.mfOfStarStrongLift` stays true and stays proved.  It is an
  implication out of a strong hypothesis, and a strong hypothesis is not a
  false one.
* `MFOfStarStrongLiftStatement` itself is not vacuous: it quantifies over any
  family with `HasMFEmbedding (A n)`, and at non-matrix models — a norm corona,
  say, which `HNNCoronaConjugatorSentenceAudit.normMatrixCorona_hasMFEmbedding_of_positive`
  makes admissible — the hypothesis is satisfiable.  It is the *printed*
  instantiation `A n = M_{kₙ}` that is unreachable.
* Shulman's Theorem 4 is not stated with a `*`-homomorphism.  It is stated with
  a **discrete asymptotic homomorphism** `A → 𝒟`, as the docstring of
  `Analysis/ShulmanFillSymmetricDoubleFlip` records: a family `φ_t : A → 𝒟` of
  contractive maps whose multiplicativity and linearity defects vanish in the
  limit, with `q ∘ φ_t → π` pointwise.  Asymptotic multiplicativity is exactly
  what the coordinate argument above cannot exploit, because `φ_t` composed
  with a coordinate is not a homomorphism.  So the repair is not to weaken
  `MFOfStarStrongLiftStatement` but to build the asymptotic vocabulary; the
  repository has the corona-valued special case in
  `MFAlgebraAmalgamCriterion.exists_compatible_asymptotic_amalgam_model` and
  nothing for `𝒟`.

## Consequence for the lane

`ShulmanFill.ConjugatedPairFaithfulStatement` — Shulman's Theorem 10 in corona
vocabulary — cannot be discharged through `StarStrong.mfOfStarStrongLift` at
matrix models.  Any route to it has to pass through the asymptotic form of
Theorem 4 first.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

/-! ## Coordinate evaluation on the bounded product -/

section Coordinate

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
-- `lp _ ∞` is a unital ring only when its factors are, so the `𝒟` API now
-- carries this; `StarStrongLimitNorm` declares it the same way.
variable [∀ n, Nontrivial (A n)]

/-- **Coordinate evaluation on `∏ₙ A n`, as a unital `*`-homomorphism.**  Every
clause is `rfl`: the operations of the `ℓ∞`-product are coordinatewise. -/
def boundedStarSequenceCoord (n : ℕ) :
    StarStrong.BoundedStarSequence A →⋆ₐ[ℂ] A n where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem boundedStarSequenceCoord_apply (n : ℕ)
    (a : StarStrong.BoundedStarSequence A) :
    boundedStarSequenceCoord n a = a n := rfl

end Coordinate

/-! ## The coordinates of a `𝒟`-lift -/

section Lift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
-- `lp _ ∞` is a unital ring only when its factors are, so the `𝒟` API now
-- carries this; `StarStrongLimitNorm` declares it the same way.
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- **The `n`-th coordinate of `𝒟`, as a unital `*`-homomorphism `𝒟 → A n`.**
`𝒟` is a star subalgebra of the bounded product, so this is coordinate
evaluation restricted along the inclusion. -/
def starStrongCoord (n : ℕ) :
    StarStrong.starStrongSubalgebra ι hnorm hone →⋆ₐ[ℂ] A n :=
  (boundedStarSequenceCoord n).comp
    (StarStrong.starStrongSubalgebra ι hnorm hone).subtype

@[simp] theorem starStrongCoord_apply (n : ℕ)
    (x : StarStrong.starStrongSubalgebra ι hnorm hone) :
    starStrongCoord ι hnorm hone n x =
      (x : StarStrong.BoundedStarSequence A) n := rfl

variable {B : Type v} [CStarAlgebra B]

/-- **A `*`-homomorphic `𝒟`-lift with faithful `*`-strong limit is separated by
its coordinates.**  A nonzero element of the source is nonzero in some
coordinate: were all its coordinates zero, its coordinate norms would be the
constant zero sequence, so `q` would kill it, and `q ∘ ρ` is faithful. -/
theorem exists_nonzero_starStrongCoord_of_ne_zero
    (rho : B →⋆ₐ[ℂ] StarStrong.starStrongSubalgebra ι hnorm hone)
    (hfaithful : Function.Injective fun b : B ↦
      StarStrong.starStrongLimitHom ι hnorm hone (rho b))
    {b : B} (hb : b ≠ 0) :
    ∃ n : ℕ, starStrongCoord ι hnorm hone n (rho b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hb
  have hzero : ∀ n : ℕ,
      ((rho b : StarStrong.starStrongSubalgebra ι hnorm hone) :
        StarStrong.BoundedStarSequence A) n = 0 := hcon
  have hnormzero : (fun n : ℕ ↦
      ‖((rho b : StarStrong.starStrongSubalgebra ι hnorm hone) :
        StarStrong.BoundedStarSequence A) n‖) = fun _ : ℕ ↦ (0 : ℝ) := by
    funext n
    rw [hzero n, norm_zero]
  have htend : Tendsto (fun n : ℕ ↦
      ‖((rho b : StarStrong.starStrongSubalgebra ι hnorm hone) :
        StarStrong.BoundedStarSequence A) n‖) atTop (𝓝 0) := by
    rw [hnormzero]
    exact tendsto_const_nhds
  have hq : StarStrong.starStrongLimit ι hnorm hone (rho b) = 0 :=
    StarStrong.starStrongLimit_eq_zero_of_tendsto_norm_zero ι hnorm hone _ htend
  apply hfaithful
  show StarStrong.starStrongLimitHom ι hnorm hone (rho b) =
    StarStrong.starStrongLimitHom ι hnorm hone (rho 0)
  rw [map_zero, map_zero]
  exact hq

/-- **The source of a faithful `𝒟`-lift is residually `(A n)`.**  The
coordinate representations separate its points. -/
theorem eq_of_forall_starStrongCoord_eq
    (rho : B →⋆ₐ[ℂ] StarStrong.starStrongSubalgebra ι hnorm hone)
    (hfaithful : Function.Injective fun b : B ↦
      StarStrong.starStrongLimitHom ι hnorm hone (rho b))
    {b₁ b₂ : B}
    (h : ∀ n : ℕ, starStrongCoord ι hnorm hone n (rho b₁) =
      starStrongCoord ι hnorm hone n (rho b₂)) :
    b₁ = b₂ := by
  have hsub : b₁ - b₂ = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ :=
      exists_nonzero_starStrongCoord_of_ne_zero ι hnorm hone rho hfaithful hne
    apply hn
    rw [map_sub, map_sub, h n, sub_self]
  exact eq_of_sub_eq_zero hsub

/-- **The obstruction.**  An algebra with no nonzero representation in any
model `A n` has no `*`-homomorphic `𝒟`-lift with faithful `*`-strong limit,
unless it is the zero algebra.

At the printed family `A n = M_{kₙ}` the hypothesis says that `B` has no
nonzero finite-dimensional representation, which holds for every simple
infinite-dimensional `B` — `C*_r(F_2)` in particular, which is MF.  So the
`*`-homomorphic reading of the lifting direction of Shulman's Theorem 4 is
false at the family that theorem is about. -/
theorem eq_zero_of_forall_hom_to_model_eq_zero
    (hmodels : ∀ (n : ℕ) (f : B →⋆ₐ[ℂ] A n) (x : B), f x = 0)
    (rho : B →⋆ₐ[ℂ] StarStrong.starStrongSubalgebra ι hnorm hone)
    (hfaithful : Function.Injective fun b : B ↦
      StarStrong.starStrongLimitHom ι hnorm hone (rho b))
    (b : B) : b = 0 := by
  by_contra hb
  obtain ⟨n, hn⟩ :=
    exists_nonzero_starStrongCoord_of_ne_zero ι hnorm hone rho hfaithful hb
  exact hn (hmodels n ((starStrongCoord ι hnorm hone n).comp rho) b)

end Lift

end

end ShulmanFill
end GroupApproximation
