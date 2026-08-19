import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# `lem:ultrafinite` at arbitrary finite-dimensional Hilbert blocks

The manuscript's finiteness lemma is printed for **abstract** finite-dimensional
Hilbert spaces:

> Let `(K_n)` be finite-dimensional Hilbert spaces and let
> `B_c = ∏_n B(K_n) / ⨁_n B(K_n)` be the quotient of the bounded family algebra
> by the `c₀`-sum.  Then `B_c` is a finite `C*`-algebra: every `σ ∈ B_c` with
> `σ*σ = 1` satisfies `σσ* = 1`.

and its proof is printed at the level of representatives:

> Lift `σ` to a bounded family `(σ_n)`.  Then `‖σ_n^*σ_n - 1‖ → 0`, so for all
> large `n` the Gram defect is at most `1/2` and `σ_n^*σ_n` is invertible; each
> `σ_n` acts on a finite-dimensional space, so polar correction replaces it by a
> unitary `w_n = σ_n(σ_n^*σ_n)^{-1/2}` with `‖σ_n - w_n‖ → 0`.  Hence `σ` is the
> class of `(w_n)`, and `w_nw_n^* = 1` at every such `n` gives `σσ^* = 1`.

`Sofic/UltraproductDedekindFinite.kt_06_ultraproduct_finite` proves this for
**matrix** blocks `M_{d_n}(ℂ)`.  Abstract finite-dimensional Hilbert spaces are
strictly broader than coordinatized matrix algebras, and the coordinatization is
a bridge nobody had crossed.  This file removes the gap by *not* crossing it:
the argument is carried out at the abstract blocks directly.

## What the finite dimension is for

Exactly one thing, and it is isolated here as a hypothesis on the blocks:

`hDF : ∀ a b, a * b = 1 → b * a = 1`  (Dedekind finiteness),

together with the observation that the polar correction of an *approximate
isometry* is an isometry outright.  `star_polarUnitary_mul_self` proves
`w^*w = 1` from the single printed bound `‖x^*x - 1‖ ≤ 1/2` -- the second Gram
bound that `PolarLiftingGeneralCStar.polarUnitary_mem_unitary` asks for is not
available here, because an isometry of the corona need not be a unitary until
after the argument is finished.  Dedekind finiteness of the block then upgrades
`w^*w = 1` to `ww^* = 1`, and `continuousLinearMap_mul_eq_one_symm` proves that
for `B(K)` with `K` finite-dimensional from injective-iff-surjective.

## Statements

* `norm_mul_star_sub_one_le` -- the pointwise estimate
  `‖xx^* - 1‖ ≤ 12‖x^*x - 1‖` in a Dedekind-finite `C*`-algebra, for
  `‖x^*x - 1‖ ≤ 1/2`.  The constant is explicit and dimension-free.
* `tendsto_norm_mul_star_sub_one` -- the printed lemma at an arbitrary filter
  and arbitrary Dedekind-finite blocks.
* `manuscript_blockFamily_finite` -- the printed lemma at the printed blocks:
  arbitrary finite-dimensional complex Hilbert spaces `K_n`, at the printed
  filter `cofinite`, whose null ideal *is* the printed `c₀`-sum `⨁_nB(K_n)`.
  Membership of a bounded family in that ideal is by definition the vanishing of
  the coordinate norms, so the two displayed `Tendsto` statements are literally
  `σ^*σ = 1` and `σσ^* = 1` in `B_c`.

Nothing here is conditional and nothing is assumed: there is no boundedness
hypothesis (`‖σ_n‖ ≤ 2` is *derived* on the good set), no nondegeneracy
hypothesis on the blocks, and no separability.  `[∀ n, CompleteSpace (K n)]`
appears only because mathlib records `FiniteDimensional.complete` as a theorem
rather than an instance, so the adjoint on `K n →L[ℂ] K n` -- which occurs in
the statement -- cannot otherwise be elaborated.
-/

namespace GroupApproximation
namespace FiniteBlockCorona

open Filter
open PolarLiftingGeneralCStar

noncomputable section

/-! ## Two facts about an arbitrary `C*`-algebra -/

section Pointwise

variable {A : Type*} [CStarAlgebra A]

/-- In a `C*`-algebra the unit has norm at most one, with **no** nontriviality
hypothesis: the `C*`-identity gives `‖1‖ = ‖1‖²`, so `‖1‖ ∈ {0,1}`, and the zero
algebra realizes the first case.  Mathlib's `norm_one` needs `NormOneClass`,
which for a `C*`-algebra is exactly nontriviality. -/
theorem norm_one_le_of_cstar : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖(1 : A)‖ = ‖(1 : A)‖ * ‖(1 : A)‖ := by
    have h0 : ‖star (1 : A) * (1 : A)‖ = ‖(1 : A)‖ * ‖(1 : A)‖ :=
      CStarRing.norm_star_mul_self (x := (1 : A))
    rwa [star_one, one_mul] at h0
  nlinarith [norm_nonneg (1 : A)]

/-- An approximate isometry has norm at most two: `‖x‖² = ‖x^*x‖ ≤ 3/2`.  The
printed proof of `lem:ultrafinite` says "lift `σ` to a *bounded* family", but
boundedness of the lift is a consequence of the Gram bound rather than a
hypothesis, and this is where that is recorded. -/
theorem norm_le_two_of_gram_le {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    ‖x‖ ≤ 2 := by
  have hone : ‖(1 : A)‖ ≤ 1 := norm_one_le_of_cstar
  have h : ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self (x := x)
  have hrw : (star x * x - 1) + 1 = star x * x := by abel
  have hb : ‖star x * x‖ ≤ ‖star x * x - 1‖ + ‖(1 : A)‖ := by
    calc ‖star x * x‖ = ‖(star x * x - 1) + 1‖ := by rw [hrw]
      _ ≤ ‖star x * x - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
  nlinarith [norm_nonneg x]

/-- **The polar correction of an approximate isometry is an isometry.**  This is
`PolarLiftingGeneralCStar.polarUnitary_mem_unitary` with its second hypothesis
removed: the identity `w^*w = 1` needs only the Gram bound on `x^*x`, and it is
the half that survives when `x` is merely an approximate isometry. -/
theorem star_polarUnitary_mul_self {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    star (polarUnitary x) * polarUnitary x = 1 := by
  have hsa : IsSelfAdjoint (polarInvSqrt x) := polarInvSqrt_isSelfAdjoint x
  calc star (polarUnitary x) * polarUnitary x
      = star (x * polarInvSqrt x) * (x * polarInvSqrt x) := rfl
    _ = polarInvSqrt x * (star x * x) * polarInvSqrt x := by
        rw [star_mul, hsa.star_eq]
        simp only [mul_assoc]
    _ = 1 := polarInvSqrt_gram_polarInvSqrt hx

/-- **The printed estimate, in a Dedekind-finite block.**  If `x` is an
approximate isometry -- `‖x^*x - 1‖ ≤ 1/2` -- and the ambient algebra is
Dedekind finite, then the *other* Gram defect is bounded by the first, with an
explicit dimension-free constant.

This is the whole content of the printed sentence "each `σ_n` acts on a
finite-dimensional space, so polar correction replaces it by a unitary `w_n`
with `‖σ_n - w_n‖ → 0`": the polar correction is an isometry by
`star_polarUnitary_mul_self`, Dedekind finiteness makes it a unitary, and the
printed perturbation estimate transfers the bound. -/
theorem norm_mul_star_sub_one_le (hDF : ∀ a b : A, a * b = 1 → b * a = 1)
    {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    ‖x * star x - 1‖ ≤ 12 * ‖star x * x - 1‖ := by
  have hone : ‖(1 : A)‖ ≤ 1 := norm_one_le_of_cstar
  set w := polarUnitary x
  have hw1 : star w * w = 1 := star_polarUnitary_mul_self hx
  have hw2 : w * star w = 1 := hDF (star w) w hw1
  have hwn : ‖w‖ ≤ 1 := by
    have h : ‖star w * w‖ = ‖w‖ * ‖w‖ := CStarRing.norm_star_mul_self (x := w)
    rw [hw1] at h
    nlinarith [norm_nonneg w]
  have hxn : ‖x‖ ≤ 2 := norm_le_two_of_gram_le hx
  have hd : ‖w - x‖ ≤ 2 * ‖x‖ * ‖star x * x - 1‖ := norm_polarUnitary_sub_le hx
  have hd4 : ‖w - x‖ ≤ 4 * ‖star x * x - 1‖ := by
    have hprod : 0 ≤ (2 - ‖x‖) * ‖star x * x - 1‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    nlinarith [hd]
  have hsplit : x * star x - 1 = x * (star x - star w) + (x - w) * star w := by
    rw [← hw2, mul_sub, sub_mul]
    abel
  have key : ‖x * star x - 1‖ ≤ ‖x‖ * ‖w - x‖ + ‖w - x‖ * ‖w‖ := by
    have h1 : ‖star x - star w‖ = ‖w - x‖ := by
      rw [← star_sub, norm_star]
      exact norm_sub_rev x w
    have h2 : ‖star w‖ = ‖w‖ := norm_star w
    calc ‖x * star x - 1‖
        = ‖x * (star x - star w) + (x - w) * star w‖ := by rw [hsplit]
      _ ≤ ‖x * (star x - star w)‖ + ‖(x - w) * star w‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖star x - star w‖ + ‖x - w‖ * ‖star w‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖x‖ * ‖w - x‖ + ‖w - x‖ * ‖w‖ := by
          rw [h1, h2, norm_sub_rev x w]
  nlinarith [key, hd4, norm_nonneg (w - x), norm_nonneg (star x * x - 1),
    mul_le_mul_of_nonneg_right hxn (norm_nonneg (w - x)),
    mul_le_mul_of_nonneg_left hwn (norm_nonneg (w - x))]

end Pointwise

/-! ## The printed lemma over a family of blocks -/

/-- **`lem:ultrafinite`, at arbitrary Dedekind-finite blocks and an arbitrary
filter.**  If every coordinate algebra is Dedekind finite then an approximate
isometry of the corona is an approximate co-isometry: the two displayed limits
are exactly `σ^*σ = 1` and `σσ^* = 1` in `(∏_nB_n)/(⨁_lB_n)`, because
membership in the null ideal *is* the vanishing of the coordinate norms.

No boundedness hypothesis on `x` occurs: on the set where the first Gram defect
is at most `1/2` the bound `‖x_n‖ ≤ 2` is a consequence, not an assumption. -/
theorem tendsto_norm_mul_star_sub_one {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)]
    (hDF : ∀ n, ∀ a b : B n, a * b = 1 → b * a = 1)
    (l : Filter ℕ) (x : ∀ n, B n)
    (h : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) l (nhds 0)) :
    Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) l (nhds 0) := by
  have hgood : ∀ᶠ n in l, ‖star (x n) * x n - 1‖ ≤ 1 / 2 := by
    have hd := (Metric.tendsto_nhds.mp h) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine squeeze_zero' (g := fun n ↦ 12 * ‖star (x n) * x n - 1‖)
    (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [hgood] with n hn
    exact norm_mul_star_sub_one_le (hDF n) hn
  · simpa using h.const_mul (12 : ℝ)

/-! ## The printed blocks: bounded operators on a finite-dimensional space -/

/-- **`B(K)` is Dedekind finite for `K` finite-dimensional.**  A left inverse of
a continuous operator on a finite-dimensional space is a two-sided inverse:
`f ∘ g = id` makes `f` surjective, hence injective, and cancelling `f` from
`f(g(f v)) = f v` gives `g ∘ f = id`.

This is the *only* place the finite dimension of the printed `K_n` is used. -/
theorem continuousLinearMap_mul_eq_one_symm {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] (f g : K →L[ℂ] K)
    (h : f * g = 1) : g * f = 1 := by
  have happ : ∀ v : K, f (g v) = v := by
    intro v
    have hv : (f * g) v = (1 : K →L[ℂ] K) v := by rw [h]
    exact hv
  have hsurj : Function.Surjective ⇑(f.toLinearMap) := fun v ↦ ⟨g v, happ v⟩
  have hinj : Function.Injective ⇑(f.toLinearMap) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  ext v
  have h1 : f.toLinearMap (g (f v)) = f.toLinearMap v := happ (f v)
  exact hinj h1

/-- **The printed lemma at the printed blocks.**  Let `(K_n)` be *arbitrary*
finite-dimensional complex Hilbert spaces and let
`B_c = ∏_nB(K_n)/⨁_nB(K_n)`.  Then `B_c` is a finite `C*`-algebra: an element
`σ` with `σ^*σ = 1` satisfies `σσ^* = 1`.

The two hypotheses-free `Tendsto` statements are the two identities in `B_c`,
written on a representative family `(σ_n)` exactly as the printed proof writes
them; the `c₀`-sum `⨁_nB(K_n)` is by definition the family algebra's null ideal
at `cofinite`.

The blocks here are not coordinatized: no orthonormal basis is chosen and no
identification `B(K_n) ≅ M_{d_n}(ℂ)` is used, so this is the printed statement
and not its matrix specialization. -/
theorem manuscript_blockFamily_finite (K : ℕ → Type*)
    [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    [∀ n, CompleteSpace (K n)] [∀ n, FiniteDimensional ℂ (K n)]
    (σ : ∀ n, K n →L[ℂ] K n)
    (h : Tendsto (fun n ↦ ‖star (σ n) * σ n - 1‖) cofinite (nhds 0)) :
    Tendsto (fun n ↦ ‖σ n * star (σ n) - 1‖) cofinite (nhds 0) :=
  tendsto_norm_mul_star_sub_one
    (fun n a b hab ↦ continuousLinearMap_mul_eq_one_symm a b hab) cofinite σ h

/-- The same statement at an arbitrary filter, which is what the manuscript's
`ω`-version of the paragraph -- "the same polar-correction argument shows that
`B_ω` is finite, with ordinary eventual convergence replaced by convergence
along `ω`" -- asserts.  One proof serves both: the filter is a parameter
throughout. -/
theorem manuscript_blockFamily_finite_filter (K : ℕ → Type*)
    [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    [∀ n, CompleteSpace (K n)] [∀ n, FiniteDimensional ℂ (K n)]
    (l : Filter ℕ) (σ : ∀ n, K n →L[ℂ] K n)
    (h : Tendsto (fun n ↦ ‖star (σ n) * σ n - 1‖) l (nhds 0)) :
    Tendsto (fun n ↦ ‖σ n * star (σ n) - 1‖) l (nhds 0) :=
  tendsto_norm_mul_star_sub_one
    (fun n a b hab ↦ continuousLinearMap_mul_eq_one_symm a b hab) l σ h

end

end FiniteBlockCorona
end GroupApproximation
