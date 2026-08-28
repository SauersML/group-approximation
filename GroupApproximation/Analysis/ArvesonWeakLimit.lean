import GroupApproximation.Analysis.ArvesonBHTarget

/-!
# The limit step of Arveson's theorem, reduced to one Hilbert-space fact

`Analysis/ArvesonBHTarget` proves Arveson's extension theorem at a `B(H)`
target from `ArvesonLimitStatement`, the step that produces a point-weak\*
cluster point of a sequence of form-positive maps.  That statement mixes two
things: a genuine piece of Hilbert-space analysis, and bookkeeping about
limits.  This module separates them.

* `WeakClusterStatement` is the analysis, and nothing else: a uniformly bounded
  sequence of linear maps `A → B(H)` has a linear map `Ψ : A → B(H)` whose
  matrix coefficients are the coefficients' limits along some ultrafilter
  refining `atTop`.  It is Banach--Alaoglu followed by Riesz: for each `(x, v,
  w)` the coefficients `⟪v, Ψₙ(x) w⟫` lie in a fixed closed ball of `ℂ`, so
  they have a limit along any ultrafilter; that limit is sesquilinear in
  `(v, w)` and bounded by `‖x‖ ‖v‖ ‖w‖`, so it is `⟪v, T w⟫` for a unique
  bounded `T`; and `x ↦ T` is linear because limits are.  Mathlib's entry point
  for the last step is `InnerProductSpace.toDual`.
* `arvesonLimit_of_weakCluster` is the bookkeeping, proved here: form
  positivity passes to the limit because a limit of numbers with nonnegative
  real part has nonnegative real part; and the two convergence hypotheses,
  which hold along `atTop`, hold along the finer ultrafilter, so uniqueness of
  limits identifies `Ψ` with `1` at the unit and with `Φ` on the subalgebra.

So what the Arveson lane still owes is exactly `WeakClusterStatement`: one
statement about bounded operators on a Hilbert space, with no completely
positive map, no subalgebra and no C\*-algebra in it.

## A note on the uniform bound

`ArvesonLimitStatement` carries the hypothesis `‖Ψₙ x‖ ≤ ‖x‖` because form
positivity alone does not bound a map — Kadison--Schwarz bounds it in terms of
its value at `1`, and the bound this repository has,
`CStarUnitalCPContractive.IsCompletelyPositive.norm_apply_le_of_unital`, is for
unital completely positive maps.  `arvesonBH_of_limit` discharges it, since its
approximants are dilations of exactly such maps.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.  The names carrying risk are
`tendsto_finset_sum`, `ge_of_tendsto`, `Complex.continuous_re`,
`Filter.Tendsto.mono_left`, `tendsto_nhds_unique` and `ext_inner_left`.
-/

namespace GroupApproximation
namespace CStarExactness

open Filter Topology

open scoped InnerProductSpace

noncomputable section

/-- **The Banach--Alaoglu step of Arveson's theorem, isolated.**  A uniformly
bounded sequence of linear maps into `B(H)` has a weak cluster point, along an
ultrafilter refining `atTop`. -/
def WeakClusterStatement : Prop :=
  ∀ {A : Type} [CStarAlgebra A] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (Psi : ℕ → (A →ₗ[ℂ] (H →L[ℂ] H))),
    (∀ (n : ℕ) (x : A), ‖Psi n x‖ ≤ ‖x‖) →
      ∃ (Ψ : A →ₗ[ℂ] (H →L[ℂ] H)) (u : Ultrafilter ℕ),
        (u : Filter ℕ) ≤ atTop ∧
          ∀ (x : A) (v w : H),
            Tendsto (fun n ↦ ⟪v, Psi n x w⟫_ℂ) (u : Filter ℕ)
              (𝓝 ⟪v, Ψ x w⟫_ℂ)

/-- **The limit step, from the cluster point.**  Everything except the cluster
point itself is limit arithmetic. -/
theorem arvesonLimit_of_weakCluster (hcl : WeakClusterStatement) :
    ArvesonLimitStatement := by
  intro A _ H _ _ _ C Φ Psi hCP hbound hone hCsub
  obtain ⟨Ψ, u, hu, hlim⟩ := hcl Psi hbound
  haveI : (u : Filter ℕ).NeBot := u.neBot
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · -- form positivity survives the limit
    intro m a v
    have hsum : Tendsto
        (fun n ↦ ∑ i : Fin m, ∑ j : Fin m,
          ⟪v i, Psi n (star (a i) * a j) (v j)⟫_ℂ) (u : Filter ℕ)
        (𝓝 (∑ i : Fin m, ∑ j : Fin m,
          ⟪v i, Ψ (star (a i) * a j) (v j)⟫_ℂ)) := by
      refine tendsto_finset_sum _ fun i _ ↦ ?_
      exact tendsto_finset_sum _ fun j _ ↦ hlim (star (a i) * a j) (v i) (v j)
    have hre := (Complex.continuous_re.tendsto _).comp hsum
    refine ge_of_tendsto hre ?_
    filter_upwards with n
    exact hCP n m a v
  · -- the limit is unital
    refine ContinuousLinearMap.ext fun w ↦ ?_
    refine ext_inner_left ℂ fun v ↦ ?_
    have h1 : Tendsto (fun n ↦ ⟪v, Psi n 1 w⟫_ℂ) (u : Filter ℕ)
        (𝓝 ⟪v, w⟫_ℂ) := (hone v w).mono_left hu
    exact tendsto_nhds_unique (hlim 1 v w) h1
  · -- the limit extends `Φ`
    intro c
    refine ContinuousLinearMap.ext fun w ↦ ?_
    refine ext_inner_left ℂ fun v ↦ ?_
    have h1 : Tendsto (fun n ↦ ⟪v, Psi n (c : A) w⟫_ℂ) (u : Filter ℕ)
        (𝓝 ⟪v, Φ c w⟫_ℂ) := (hCsub c v w).mono_left hu
    exact tendsto_nhds_unique (hlim (c : A) v w) h1

/-- **Arveson's extension theorem at a `B(H)` target, from the cluster
point.**  Composing the two reductions: what is left of Arveson at `B(H)` is
`WeakClusterStatement` and nothing else. -/
theorem arvesonBH_of_weakCluster (hcl : WeakClusterStatement) :
    ∀ {A : Type} [CStarAlgebra A] {H : Type} [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H]
      (C : StarSubalgebra ℂ A), IsClosed (C : Set A) →
      ∀ (Φ : ↥C →ₗ[ℂ] (H →L[ℂ] H)), IsFormCP Φ →
        (∀ c : ↥C, Φ (star c) = star (Φ c)) → Φ 1 = 1 →
        ∀ (k : ℕ → ℕ) (J : ∀ n, EuclideanSpace ℂ (Fin (k n)) →L[ℂ] H),
          (∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin (k n))),
            (ContinuousLinearMap.adjoint (J n)) (J n v) = v) →
          (∀ n : ℕ, ‖J n‖ ≤ 1) →
          (∀ v w : H,
            Tendsto (fun n ↦
              ⟪v, ((J n).comp (ContinuousLinearMap.adjoint (J n))) w⟫_ℂ)
              atTop (𝓝 ⟪v, w⟫_ℂ)) →
          (∀ (c : ↥C) (v w : H),
            Tendsto (fun n ↦
              ⟪v, (J n) ((isometryCompress (J n) Φ c)
                ((ContinuousLinearMap.adjoint (J n)) w))⟫_ℂ)
              atTop (𝓝 ⟪v, Φ c w⟫_ℂ)) →
          ∃ Ψ : A →ₗ[ℂ] (H →L[ℂ] H), IsFormCP Ψ ∧ Ψ 1 = 1 ∧
            ∀ c : ↥C, Ψ (c : A) = Φ c := by
  intro A _ H _ _ _ C hC Φ hform hstar hone k J hJ hJnorm hWOTone hWOT
  exact arvesonBH_of_limit (arvesonLimit_of_weakCluster hcl) C hC Φ hform hstar
    hone k J hJ hJnorm hWOTone hWOT

end

end CStarExactness
end GroupApproximation
