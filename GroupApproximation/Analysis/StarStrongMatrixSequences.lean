import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# `*`-strong convergence of a bounded sequence of operators

Shulman's algebra `𝒟` is the set of bounded sequences of matrices whose images
in `B(H)` converge `*`-strongly.  This file is the operator half of that
construction: everything about `*`-strong convergence of a sequence
`S : ℕ → B(H)` that does not mention the sequence algebra.

## What `*`-strong means here, and why

`Sₙ → T` `*`-strongly is `Sₙ v → T v` and `Sₙ* v → T* v` for every `v`.  Both
halves are stated as pointwise convergence in `H`, not as convergence in a
topology on `B(H)`: the strong operator topology is a topology on a space of
maps, and every statement below is about one vector at a time, so naming the
topology would buy nothing and cost an instance.

Three facts carry the whole construction.

* **Limits are unique** (`IsStarStrongLimit.unique`): two `*`-strong limits
  agree at every vector, and a bounded operator is its action on vectors.
* **Products pass to the limit when the factors are uniformly bounded**
  (`IsStarStrongLimit.mul`).  This is the one place a bound is needed, and it
  is needed: `Sₙ(wₙ) - T(w₀) = Sₙ(wₙ - w₀) + (Sₙ w₀ - T w₀)`, and the first
  term is controlled only by `‖Sₙ‖ ‖wₙ - w₀‖`.  The adjoint half needs the
  same bound on the other factor, since `(S₁S₂)* = S₂*S₁*`.
* **A uniformly bounded, pointwise Cauchy sequence has a `*`-strong limit**
  (`exists_isStarStrongLimit`).  `H` is complete, so each `Sₙ v` converges;
  the limit function is linear because limits are, and bounded by the uniform
  bound, so it is a bounded operator `T`.  The adjoint sequence converges the
  same way to some `G`, and `G = T*` because the inner product is continuous:

      ⟪G x, y⟫ = lim ⟪Sₙ* x, y⟫ = lim ⟪x, Sₙ y⟫ = ⟪x, T y⟫ .

That last fact is what makes the closure of `𝒟` an `ε/3` argument rather than
a construction: once a sequence is known to be pointwise Cauchy, its limit
operator comes for free.

## A note on spelling

The algebraic identities `(S + S') v = S v + S' v`, `(c • S) v = c • S v` and
`(S * S') v = S (S' v)` hold definitionally for continuous linear maps, so
they are used through `exact` rather than through the corresponding
`ContinuousLinearMap` simp lemmas.  That is not stylistic: those lemmas are
being renamed upstream, and a proof that leans on `rfl` cannot be broken by a
rename.  The `star` identities are genuine rewrites -- the adjoint of a sum is
not the sum of the adjoints by definition -- and are taken from the stable
`StarAddMonoid` / `StarMul` API.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- The adjoint is an isometry, so a bound on an operator is a bound on its
adjoint. -/
theorem norm_star_le_of_norm_le {A : H →L[ℂ] H} {C : ℝ} (h : ‖A‖ ≤ C) :
    ‖star A‖ ≤ C := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (le_of_eq (ContinuousLinearMap.adjoint.norm_map A)).trans h

/-- `T` is the `*`-strong limit of the sequence `S`: the sequence and its
adjoint sequence converge pointwise, to `T` and to `T*`. -/
def IsStarStrongLimit (S : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H) : Prop :=
  (∀ v : H, Tendsto (fun n ↦ S n v) atTop (𝓝 (T v))) ∧
    ∀ v : H, Tendsto (fun n ↦ (star (S n)) v) atTop (𝓝 ((star T) v))

/-- A `*`-strong limit is unique: a bounded operator is its action on
vectors. -/
theorem IsStarStrongLimit.unique {S : ℕ → H →L[ℂ] H} {T₁ T₂ : H →L[ℂ] H}
    (h₁ : IsStarStrongLimit S T₁) (h₂ : IsStarStrongLimit S T₂) : T₁ = T₂ := by
  ext v
  exact tendsto_nhds_unique (h₁.1 v) (h₂.1 v)

theorem IsStarStrongLimit.star {S : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (h : IsStarStrongLimit S T) :
    IsStarStrongLimit (fun n ↦ star (S n)) (star T) :=
  ⟨h.2, by simpa only [star_star] using h.1⟩

/-- Transport a `*`-strong limit along a pointwise equality of sequences.
Used whenever a sequence is rewritten by a homomorphism identity such as
`ι n ((a * b) n) = ι n (a n) * ι n (b n)`. -/
theorem IsStarStrongLimit.congr {S S' : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hSS' : ∀ n, S n = S' n) (h : IsStarStrongLimit S T) :
    IsStarStrongLimit S' T := by
  have hfun : S = S' := funext hSS'
  exact hfun ▸ h

theorem isStarStrongLimit_zero :
    IsStarStrongLimit (fun _ : ℕ ↦ (0 : H →L[ℂ] H)) 0 :=
  ⟨fun _ ↦ tendsto_const_nhds, fun _ ↦ tendsto_const_nhds⟩

theorem IsStarStrongLimit.add {S₁ S₂ : ℕ → H →L[ℂ] H} {T₁ T₂ : H →L[ℂ] H}
    (h₁ : IsStarStrongLimit S₁ T₁) (h₂ : IsStarStrongLimit S₂ T₂) :
    IsStarStrongLimit (fun n ↦ S₁ n + S₂ n) (T₁ + T₂) := by
  constructor
  · intro v
    exact (h₁.1 v).add (h₂.1 v)
  · intro v
    simpa only [star_add, _root_.add_apply] using (h₁.2 v).add (h₂.2 v)

theorem IsStarStrongLimit.smul {S : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H} (c : ℂ)
    (h : IsStarStrongLimit S T) :
    IsStarStrongLimit (fun n ↦ c • S n) (c • T) := by
  constructor
  · intro v
    exact (h.1 v).const_smul c
  · intro v
    simpa only [star_smul, _root_.smul_apply] using (h.2 v).const_smul (Star.star c)

omit [CompleteSpace H] in
/-- A uniformly bounded sequence of operators may be evaluated along a
convergent sequence of vectors.  The bound is what controls the diagonal error
`Sₙ(wₙ - w₀)`. -/
theorem tendsto_apply_of_norm_le {S : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H} {C : ℝ}
    (hC : ∀ n, ‖S n‖ ≤ C)
    (hS : ∀ v : H, Tendsto (fun n ↦ S n v) atTop (𝓝 (T v)))
    {w : ℕ → H} {w₀ : H} (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun n ↦ S n (w n)) atTop (𝓝 (T w₀)) := by
  have hsplit : ∀ n, S n (w n) = S n (w n - w₀) + S n w₀ := by
    intro n
    rw [← map_add]
    congr 1
    abel
  have hdiff : Tendsto (fun n ↦ ‖w n - w₀‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hw
  have hbound : Tendsto (fun n ↦ C * ‖w n - w₀‖) atTop (𝓝 0) := by
    simpa using hdiff.const_mul C
  have h1 : Tendsto (fun n ↦ S n (w n - w₀)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hbound
    exact ((S n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  simpa only [hsplit, zero_add] using h1.add (hS w₀)

/-- Products pass to the `*`-strong limit when both factors are uniformly
bounded. -/
theorem IsStarStrongLimit.mul {S₁ S₂ : ℕ → H →L[ℂ] H} {T₁ T₂ : H →L[ℂ] H}
    {C : ℝ} (hC₁ : ∀ n, ‖S₁ n‖ ≤ C) (hC₂ : ∀ n, ‖S₂ n‖ ≤ C)
    (h₁ : IsStarStrongLimit S₁ T₁) (h₂ : IsStarStrongLimit S₂ T₂) :
    IsStarStrongLimit (fun n ↦ S₁ n * S₂ n) (T₁ * T₂) := by
  constructor
  · intro v
    exact tendsto_apply_of_norm_le hC₁ h₁.1 (h₂.1 v)
  · intro v
    have h := tendsto_apply_of_norm_le
      (fun n ↦ norm_star_le_of_norm_le (hC₂ n)) h₂.2 (h₁.2 v)
    simpa only [star_mul, _root_.mul_apply_eq_comp] using h

omit [CompleteSpace H] in
/-- Pointwise Cauchy-ness is inherited from uniform approximants.  This is the
`ε/3` argument, and it is the only analytic input the closure of `𝒟` needs:
the middle third is the approximant's own Cauchy-ness, and the two outer
thirds are the uniform bound, once at `m` and once at `n`. -/
theorem cauchySeq_apply_of_approx {S : ℕ → H →L[ℂ] H} {v : H}
    (h : ∀ ε : ℝ, 0 < ε → ∃ S' : ℕ → H →L[ℂ] H,
      (∀ n, ‖S n - S' n‖ * ‖v‖ ≤ ε) ∧ CauchySeq (fun n ↦ S' n v)) :
    CauchySeq (fun n ↦ S n v) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨S', hclose, hcauchy⟩ := h (ε / 3) (by linarith)
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have key : ∀ k, dist (S k v) (S' k v) ≤ ε / 3 := by
    intro k
    have hsub : S k v - S' k v = (S k - S' k) v := rfl
    rw [dist_eq_norm, hsub]
    exact ((S k - S' k).le_opNorm v).trans (hclose k)
  have h1 : dist (S m v) (S' m v) ≤ ε / 3 := key m
  have h2 : dist (S' m v) (S' n v) < ε / 3 := hN m hm n hn
  have h3 : dist (S' n v) (S n v) ≤ ε / 3 := by
    rw [dist_comm]
    exact key n
  have t1 := dist_triangle (S m v) (S' m v) (S n v)
  have t2 := dist_triangle (S' m v) (S' n v) (S n v)
  linarith

/-! ## Existence of the limit operator -/

omit [CompleteSpace H] in
/-- A pointwise limit of a uniformly bounded sequence of operators is again a
bounded operator: it is linear because limits are, and bounded by the uniform
bound. -/
theorem exists_continuousLinearMap_of_tendsto {S : ℕ → H →L[ℂ] H} {C : ℝ}
    {f : H → H} (hC : ∀ n, ‖S n‖ ≤ C)
    (hf : ∀ v : H, Tendsto (fun n ↦ S n v) atTop (𝓝 (f v))) :
    ∃ T : H →L[ℂ] H, ∀ v : H, T v = f v := by
  have hadd : ∀ x y : H, f (x + y) = f x + f y := by
    intro x y
    refine tendsto_nhds_unique (hf (x + y)) ?_
    simpa only [map_add] using (hf x).add (hf y)
  have hsmul : ∀ (c : ℂ) (x : H), f (c • x) = c • f x := by
    intro c x
    refine tendsto_nhds_unique (hf (c • x)) ?_
    simpa only [map_smul] using (hf x).const_smul c
  have hbound : ∀ v : H, ‖f v‖ ≤ C * ‖v‖ := by
    intro v
    refine le_of_tendsto (hf v).norm (Eventually.of_forall fun n ↦ ?_)
    exact ((S n).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg v))
  exact ⟨LinearMap.mkContinuous
    { toFun := f, map_add' := hadd, map_smul' := fun c x ↦ hsmul c x }
    C hbound, fun _ ↦ rfl⟩

/-- A uniformly bounded sequence whose values and adjoint values are pointwise
Cauchy has a `*`-strong limit. -/
theorem exists_isStarStrongLimit {S : ℕ → H →L[ℂ] H} {C : ℝ}
    (hC : ∀ n, ‖S n‖ ≤ C)
    (hcauchy : ∀ v : H, CauchySeq (fun n ↦ S n v))
    (hcauchy' : ∀ v : H, CauchySeq (fun n ↦ (star (S n)) v)) :
    ∃ T : H →L[ℂ] H, IsStarStrongLimit S T := by
  classical
  obtain ⟨f, hf⟩ :
      ∃ f : H → H, ∀ v : H, Tendsto (fun n ↦ S n v) atTop (𝓝 (f v)) :=
    ⟨fun v ↦ Classical.choose (cauchySeq_tendsto_of_complete (hcauchy v)),
      fun v ↦ Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy v))⟩
  obtain ⟨g, hg⟩ :
      ∃ g : H → H,
        ∀ v : H, Tendsto (fun n ↦ (star (S n)) v) atTop (𝓝 (g v)) :=
    ⟨fun v ↦ Classical.choose (cauchySeq_tendsto_of_complete (hcauchy' v)),
      fun v ↦
        Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy' v))⟩
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_of_tendsto hC hf
  obtain ⟨G, hG⟩ := exists_continuousLinearMap_of_tendsto
    (fun n ↦ norm_star_le_of_norm_le (hC n)) hg
  have hfT : ∀ v : H, Tendsto (fun n ↦ S n v) atTop (𝓝 (T v)) := by
    intro v
    rw [hT v]
    exact hf v
  have hgG : ∀ v : H, Tendsto (fun n ↦ (star (S n)) v) atTop (𝓝 (G v)) := by
    intro v
    rw [hG v]
    exact hg v
  have hGT : G = star T := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have h1 : Tendsto (fun n ↦ ⟪(star (S n)) x, y⟫_ℂ) atTop (𝓝 ⟪G x, y⟫_ℂ) :=
      (hgG x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n ↦ ⟪x, S n y⟫_ℂ) atTop (𝓝 ⟪x, T y⟫_ℂ) :=
      tendsto_const_nhds.inner (hfT y)
    have h3 : ∀ n, ⟪(star (S n)) x, y⟫_ℂ = ⟪x, S n y⟫_ℂ := by
      intro n
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint_inner_left (S n) y x
    exact tendsto_nhds_unique h1 ((tendsto_congr h3).mpr h2)
  refine ⟨T, hfT, fun v ↦ ?_⟩
  rw [← hGT]
  exact hgG v

end

end StarStrong
end GroupApproximation
