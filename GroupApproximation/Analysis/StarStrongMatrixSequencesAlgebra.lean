import Mathlib.Analysis.CStarAlgebra.lpSpace
import GroupApproximation.Analysis.StarStrongMatrixSequences

/-!
# Shulman's algebra `𝒟` and its limit map `q`

Shulman's lifting criterion for MF algebras runs through one algebra.  Fix a
Hilbert space `H` and a sequence of C-star algebras `A n` embedded in `B(H)`
by `*`-homomorphisms `ι n` -- in the printed setting `A n = M_n` and
`ι n` is compression to the first `n` coordinates, `M_n = P_n B(H) P_n`.  Then

    𝒟 = { a ∈ ∏ₙ A n bounded | (ι n (aₙ)) converges `*`-strongly } ,
    q a = the `*`-strong limit .

This file builds `𝒟` and `q` and proves the four facts the criterion needs.

## What is proved

* `starStrongSubalgebra` -- `𝒟` is a unital star subalgebra of the bounded
  product `lp (fun n ↦ A n) ∞`.  Sums, scalar multiples and adjoints are
  immediate; products are the one step with content, and they need the uniform
  bound `‖ι n (aₙ)‖ ≤ ‖a‖` that the `ℓ∞`-product supplies for free.  The unit
  is where the embeddings' non-unitality is felt: `ι n (1)` is the projection
  `P_n`, not `1`, so `1 ∈ 𝒟` is exactly the hypothesis `P_n → 1` strongly.
* `starStrongSubalgebra_isClosed` -- `𝒟` is norm closed, by the `ε/3` argument
  of `StarStrong.cauchySeq_apply_of_approx` together with the existence of
  limit operators for pointwise Cauchy sequences.
* `starStrongLimitHom` -- `q` is a unital `*`-homomorphism `𝒟 → B(H)`.  Every
  clause is uniqueness of `*`-strong limits: the sequence attached to `x * y`
  has both `q x * q y` and `q (x * y)` as limits.
* `starStrongLimit_eq_zero_of_tendsto_norm_zero` -- norm-null sequences lie in
  `ker q`, so `q` factors through the corona `∏ₙ A n / ⨁ₙ A n`.

## Two hypotheses, and why they are hypotheses

`hnorm : ∀ n x, ‖ι n x‖ ≤ ‖x‖` is automatic -- a `*`-homomorphism of C-star
algebras is contractive -- but deriving it here would force a
`NonUnitalCStarAlgebra` instance on `H →L[ℂ] H` through the whole file for one
inequality.  Taking it as an argument keeps the instance surface at what the
statements actually mention, and any concrete family discharges it (the
compressions `M_n ↪ B(H)` are isometric).

`hone : ∀ v, ι n (1) v → v` is not automatic and not a technicality: it is the
statement that the embeddings exhaust `H`, and without it `𝒟` is not unital.
For the printed family it is `P_n → 1` strongly, which is why `H` must be the
closure of the union of the ranges.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology
open scoped ENNReal

noncomputable section

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- The bounded product `∏ₙ A n`, mathlib's dependent `ℓ∞` space. -/
abbrev BoundedStarSequence (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)] :
    Type u :=
  lp (fun n ↦ A n) ∞

/-- A bounded sequence whose image sequence converges `*`-strongly. -/
def IsStarStrongConvergent (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : BoundedStarSequence A) : Prop :=
  ∃ T : H →L[ℂ] H, IsStarStrongLimit (fun n ↦ ι n (a n)) T

/-- Every coordinate of the image sequence is bounded by the norm of the
sequence: the `ℓ∞` bound, carried across a contractive embedding. -/
theorem norm_ι_apply_le (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (a : BoundedStarSequence A) (n : ℕ) : ‖ι n (a n)‖ ≤ ‖a‖ :=
  (hnorm n (a n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a n)

/-! ## The algebraic closure properties -/

theorem isStarStrongLimit_add {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {a b : BoundedStarSequence A} {S T : H →L[ℂ] H}
    (hS : IsStarStrongLimit (fun n ↦ ι n (a n)) S)
    (hT : IsStarStrongLimit (fun n ↦ ι n (b n)) T) :
    IsStarStrongLimit (fun n ↦ ι n ((a + b) n)) (S + T) :=
  (hS.add hT).congr fun n ↦ (map_add (ι n) (a n) (b n)).symm

theorem isStarStrongLimit_smul {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {a : BoundedStarSequence A} {S : H →L[ℂ] H} (c : ℂ)
    (hS : IsStarStrongLimit (fun n ↦ ι n (a n)) S) :
    IsStarStrongLimit (fun n ↦ ι n ((c • a) n)) (c • S) :=
  (hS.smul c).congr fun n ↦ (map_smul (ι n) c (a n)).symm

theorem isStarStrongLimit_star {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {a : BoundedStarSequence A} {S : H →L[ℂ] H}
    (hS : IsStarStrongLimit (fun n ↦ ι n (a n)) S) :
    IsStarStrongLimit (fun n ↦ ι n ((star a) n)) (star S) :=
  hS.star.congr fun n ↦ (map_star (ι n) (a n)).symm

theorem isStarStrongLimit_mul {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    {a b : BoundedStarSequence A} {S T : H →L[ℂ] H}
    (hS : IsStarStrongLimit (fun n ↦ ι n (a n)) S)
    (hT : IsStarStrongLimit (fun n ↦ ι n (b n)) T) :
    IsStarStrongLimit (fun n ↦ ι n ((a * b) n)) (S * T) := by
  have hC₁ : ∀ n, ‖ι n (a n)‖ ≤ ‖a‖ + ‖b‖ := by
    intro n
    refine (norm_ι_apply_le ι hnorm a n).trans ?_
    have := norm_nonneg b
    linarith
  have hC₂ : ∀ n, ‖ι n (b n)‖ ≤ ‖a‖ + ‖b‖ := by
    intro n
    refine (norm_ι_apply_le ι hnorm b n).trans ?_
    have := norm_nonneg a
    linarith
  exact (IsStarStrongLimit.mul hC₁ hC₂ hS hT).congr fun n ↦
    (map_mul (ι n) (a n) (b n)).symm

-- `1` on the bounded product needs `NormOneClass` of every factor, which for a
-- C-star algebra is exactly nontriviality.  From here on every statement
-- mentions either the unit or the subalgebra, so the variable is introduced
-- here rather than in the block above.
variable [∀ n, Nontrivial (A n)]

/-- The unit of the bounded product converges `*`-strongly to `1` exactly when
the embeddings exhaust `H`. -/
theorem isStarStrongLimit_one {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    IsStarStrongLimit
      (fun n ↦ ι n ((1 : BoundedStarSequence A) n)) 1 := by
  have hstar : ∀ n, star (ι n ((1 : BoundedStarSequence A) n)) =
      ι n ((1 : BoundedStarSequence A) n) := by
    intro n
    rw [← map_star]
    congr 1
    -- the goal is about the coordinate of the product's unit, and `star_one`
    -- takes its algebra explicitly
    show star (1 : A n) = (1 : A n)
    exact star_one (A n)
  constructor
  · intro v
    exact hone v
  · intro v
    simp only [hstar, star_one]
    exact hone v

/-! ## The algebra `𝒟` -/

/-- **Shulman's `𝒟`.**  The bounded sequences whose image sequence converges
`*`-strongly. -/
def starStrongSubalgebra (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    StarSubalgebra ℂ (BoundedStarSequence A) where
  carrier := {a : BoundedStarSequence A | IsStarStrongConvergent ι a}
  mul_mem' {a b} ha hb := by
    obtain ⟨S, hS⟩ := ha
    obtain ⟨T, hT⟩ := hb
    exact ⟨S * T, isStarStrongLimit_mul hnorm hS hT⟩
  add_mem' {a b} ha hb := by
    obtain ⟨S, hS⟩ := ha
    obtain ⟨T, hT⟩ := hb
    exact ⟨S + T, isStarStrongLimit_add hS hT⟩
  algebraMap_mem' c := by
    refine ⟨c • 1, ?_⟩
    refine (isStarStrongLimit_smul c
      (isStarStrongLimit_one hone)).congr fun n ↦ ?_
    exact congrArg (fun z : BoundedStarSequence A ↦ ι n (z n))
      (Algebra.algebraMap_eq_smul_one
        (R := ℂ) (A := BoundedStarSequence A) c).symm
  star_mem' {a} ha := by
    obtain ⟨S, hS⟩ := ha
    exact ⟨star S, isStarStrongLimit_star hS⟩

@[simp] theorem mem_starStrongSubalgebra
    {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
    {a : BoundedStarSequence A} :
    a ∈ starStrongSubalgebra ι hnorm hone ↔ IsStarStrongConvergent ι a :=
  Iff.rfl

/-! ## `𝒟` is closed -/

/-- **`𝒟` is norm closed.**  A norm limit of `*`-strongly convergent sequences
is pointwise Cauchy by the `ε/3` argument, and a uniformly bounded pointwise
Cauchy sequence has a `*`-strong limit. -/
theorem starStrongSubalgebra_isClosed (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    IsClosed ((starStrongSubalgebra ι hnorm hone :
      StarSubalgebra ℂ (BoundedStarSequence A)) :
      Set (BoundedStarSequence A)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u a hu hlim
  have hchoice : ∀ (v : H) (ε : ℝ), 0 < ε → ∃ k, ‖a - u k‖ * ‖v‖ ≤ ε := by
    intro v ε hε
    have h0 : Tendsto (fun k ↦ ‖a - u k‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hlim).congr fun k ↦
        norm_sub_rev (u k) a
    have h1 : Tendsto (fun k ↦ ‖a - u k‖ * ‖v‖) atTop (𝓝 0) := by
      simpa using h0.mul_const ‖v‖
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h1 ε hε
    refine ⟨N, ?_⟩
    have h2 := hN N le_rfl
    have hnn : (0 : ℝ) ≤ ‖a - u N‖ * ‖v‖ := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h2
    exact h2.le
  have hsub : ∀ (k : ℕ) (n : ℕ),
      ι n (a n) - ι n ((u k) n) = ι n ((a - u k) n) := by
    intro k n
    exact (map_sub (ι n) (a n) ((u k) n)).symm
  refine exists_isStarStrongLimit (C := ‖a‖)
    (fun n ↦ norm_ι_apply_le ι hnorm a n) ?_ ?_
  · intro v
    refine cauchySeq_apply_of_approx fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := hchoice v ε hε
    obtain ⟨T, hT⟩ := hu k
    refine ⟨fun n ↦ ι n ((u k) n), fun n ↦ ?_, (hT.1 v).cauchySeq⟩
    rw [hsub k n]
    exact (mul_le_mul_of_nonneg_right (norm_ι_apply_le ι hnorm (a - u k) n)
      (norm_nonneg v)).trans hk
  · intro v
    refine cauchySeq_apply_of_approx fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := hchoice v ε hε
    obtain ⟨T, hT⟩ := hu k
    refine ⟨fun n ↦ star (ι n ((u k) n)), fun n ↦ ?_, (hT.2 v).cauchySeq⟩
    have hstarsub : star (ι n (a n)) - star (ι n ((u k) n)) =
        star (ι n ((a - u k) n)) := by
      rw [← star_sub, hsub k n]
    rw [hstarsub]
    exact (mul_le_mul_of_nonneg_right
      (norm_star_le_of_norm_le (norm_ι_apply_le ι hnorm (a - u k) n))
      (norm_nonneg v)).trans hk

/-! ## The limit map `q` -/

/-- Membership in `𝒟`, in the shape `Exists.choose` consumes: the subtype's
`property` field has `Membership.mem` at its head, and dot notation resolves on
that head, not on the existential it unfolds to. -/
theorem exists_isStarStrongLimit_of_mem (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone) :
    ∃ T : H →L[ℂ] H,
      IsStarStrongLimit (fun n ↦ ι n ((x : BoundedStarSequence A) n)) T :=
  x.property

/-- **Shulman's `q`.**  The `*`-strong limit of a member of `𝒟`. -/
def starStrongLimit (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone) : H →L[ℂ] H :=
  (exists_isStarStrongLimit_of_mem ι hnorm hone x).choose

theorem starStrongLimit_spec (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone) :
    IsStarStrongLimit
      (fun n ↦ ι n ((x : BoundedStarSequence A) n))
      (starStrongLimit ι hnorm hone x) :=
  (exists_isStarStrongLimit_of_mem ι hnorm hone x).choose_spec

/-- `q` is determined by any `*`-strong limit of the same sequence. -/
theorem starStrongLimit_eq (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone) {T : H →L[ℂ] H}
    (hT : IsStarStrongLimit (fun n ↦ ι n ((x : BoundedStarSequence A) n)) T) :
    starStrongLimit ι hnorm hone x = T :=
  (starStrongLimit_spec ι hnorm hone x).unique hT

/-- **`q` is a unital `*`-homomorphism `𝒟 → B(H)`.**  Every clause is
uniqueness of `*`-strong limits. -/
def starStrongLimitHom (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    starStrongSubalgebra ι hnorm hone →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := starStrongLimit ι hnorm hone
  map_one' :=
    starStrongLimit_eq ι hnorm hone 1 (isStarStrongLimit_one hone)
  map_mul' x y :=
    starStrongLimit_eq ι hnorm hone (x * y)
      (isStarStrongLimit_mul hnorm (starStrongLimit_spec ι hnorm hone x)
        (starStrongLimit_spec ι hnorm hone y))
  map_zero' := by
    refine starStrongLimit_eq ι hnorm hone 0 ?_
    exact isStarStrongLimit_zero.congr fun n ↦ (map_zero (ι n)).symm
  map_add' x y :=
    starStrongLimit_eq ι hnorm hone (x + y)
      (isStarStrongLimit_add (starStrongLimit_spec ι hnorm hone x)
        (starStrongLimit_spec ι hnorm hone y))
  commutes' c := by
    have hlim : (algebraMap ℂ (H →L[ℂ] H) c) = c • (1 : H →L[ℂ] H) :=
      Algebra.algebraMap_eq_smul_one c
    rw [hlim]
    refine starStrongLimit_eq ι hnorm hone (algebraMap ℂ _ c) ?_
    refine (isStarStrongLimit_smul c
      (isStarStrongLimit_one hone)).congr fun n ↦ ?_
    exact congrArg (fun z : BoundedStarSequence A ↦ ι n (z n))
      (Algebra.algebraMap_eq_smul_one
        (R := ℂ) (A := BoundedStarSequence A) c).symm
  map_star' x :=
    starStrongLimit_eq ι hnorm hone (star x)
      (isStarStrongLimit_star (starStrongLimit_spec ι hnorm hone x))

@[simp] theorem starStrongLimitHom_apply (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone) :
    starStrongLimitHom ι hnorm hone x = starStrongLimit ι hnorm hone x :=
  rfl

/-! ## The null sequences lie in the kernel -/

/-- **`q` kills the norm-null sequences**, so it factors through the corona
`∏ₙ A n / ⨁ₙ A n`. -/
theorem starStrongLimit_eq_zero_of_tendsto_norm_zero
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : starStrongSubalgebra ι hnorm hone)
    (hnull : Tendsto (fun n ↦ ‖(x : BoundedStarSequence A) n‖) atTop (𝓝 0)) :
    starStrongLimit ι hnorm hone x = 0 := by
  refine starStrongLimit_eq ι hnorm hone x ?_
  constructor
  · intro v
    show Tendsto (fun n ↦ ι n ((x : BoundedStarSequence A) n) v) atTop
      (𝓝 (0 : H))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ ‖(x : BoundedStarSequence A) n‖ * ‖v‖)
      (fun n ↦ norm_nonneg _) (fun n ↦ ?_) ?_
    · exact ((ι n ((x : BoundedStarSequence A) n)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right
          (hnorm n ((x : BoundedStarSequence A) n)) (norm_nonneg v))
    · simpa using hnull.mul_const ‖v‖
  · intro v
    rw [star_zero]
    show Tendsto (fun n ↦ (star (ι n ((x : BoundedStarSequence A) n))) v) atTop
      (𝓝 (0 : H))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ ‖(x : BoundedStarSequence A) n‖ * ‖v‖)
      (fun n ↦ norm_nonneg _) (fun n ↦ ?_) ?_
    · exact ((star (ι n ((x : BoundedStarSequence A) n))).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right
          (norm_star_le_of_norm_le (hnorm n ((x : BoundedStarSequence A) n)))
          (norm_nonneg v))
    · simpa using hnull.mul_const ‖v‖

end

end StarStrong
end GroupApproximation
