import GroupApproximation.Analysis.ArvesonBHTarget
import GroupApproximation.Analysis.ArvesonSesquilinearRiesz

/-!
# (V2) The limit step of Arveson's theorem at a `B(H)` target, discharged

`Analysis/ArvesonBHTarget` proves Arveson's extension theorem at a `B(H)` target
from its steps 1--3 together with one named `Prop`, `ArvesonLimitStatement`: a
sequence of form-positive contractions `A → B(H)` whose matrix coefficients
converge at `1` and on a subalgebra has a form-positive limit, unital, agreeing
there.  That module records the step as owed, on the ground that the standard
construction — an ultrafilter limit of the coefficients, then Riesz — needs an
API the tree had no precedent for.  Both halves are now available, so the debt
is paid here.

## The construction

The coefficients `n ↦ ⟪v, Ψₙ x w⟫` are bounded by `‖x‖ ‖v‖ ‖w‖`, because a
contraction is one, so they live in a compact ball and converge along any
ultrafilter.  Take one refining `atTop`: no separability of `A` and no diagonal
extraction is needed, and every algebraic identity becomes an identity of limits
by `tendsto_nhds_unique`, in the shape
`Analysis/ShulmanFillNormingPrintedPairCharacter` uses.

The limit `L x v w` is then a bounded sesquilinear form for each `x`, and
`Analysis/ArvesonSesquilinearRiesz` turns it into the operator `Ψ x` with
`⟪v, Ψ x w⟫ = L x v w`.  Linearity of `x ↦ Ψ x` is read off the same identities
through `ext_inner_left`: an operator is determined by its coefficients, so a
linear identity between coefficients is a linear identity between operators.

Form positivity survives because each finite double sum of coefficients is a
limit of the corresponding sums for `Ψₙ`, whose real parts are nonnegative, and
a limit of nonnegative reals is nonnegative.  Unitality and the agreement on `C`
are the two convergence hypotheses: the ultrafilter refines `atTop`, so its
limit is the assumed one, and two operators with equal coefficients are equal.

Nothing here is a weak-star compactness argument in the Banach--Alaoglu sense —
the ultrafilter supplies an honest limit rather than a cluster point, which is
all the statement asks for.
-/

namespace GroupApproximation
namespace CStarExactness

open Filter Topology

open scoped InnerProductSpace

noncomputable section

/-- **The limit of a pointwise sum**, read backwards through uniqueness: a
family that is pointwise the sum of two convergent ones has for limit the sum of
their limits.  Factored out because the identities of the limit form — one per
slot of the sesquilinear form, one per algebra operation — are all this lemma
with a different pointwise identity. -/
theorem eq_add_of_tendsto {l : Filter ℕ} [l.NeBot] {f g h : ℕ → ℂ} {a b c : ℂ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hh : Tendsto h l (𝓝 c))
    (heq : ∀ n, h n = f n + g n) : c = a + b :=
  tendsto_nhds_unique hh ((hf.add hg).congr fun n ↦ (heq n).symm)

/-- **The limit of a pointwise scalar multiple**, the same way. -/
theorem eq_const_mul_of_tendsto {l : Filter ℕ} [l.NeBot] {f h : ℕ → ℂ}
    {a c z : ℂ} (hf : Tendsto f l (𝓝 a)) (hh : Tendsto h l (𝓝 c))
    (heq : ∀ n, h n = z * f n) : c = z * a :=
  tendsto_nhds_unique hh ((hf.const_mul z).congr fun n ↦ (heq n).symm)

/-- **The limit step, discharged.**  With this, `arvesonBH_of_limit` is
unconditional and Arveson's extension theorem holds at a `B(H)` target. -/
theorem arvesonLimit : ArvesonLimitStatement := by
  intro A _ H _ _ _ C Φ Psi hform hbound hone hCconv
  classical
  -- the coefficients are uniformly bounded
  have hcoeff : ∀ (x : A) (v w : H) (n : ℕ),
      ‖⟪v, Psi n x w⟫_ℂ‖ ≤ ‖x‖ * ‖v‖ * ‖w‖ := by
    intro x v w n
    calc ‖⟪v, Psi n x w⟫_ℂ‖ ≤ ‖v‖ * ‖(Psi n x) w‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖Psi n x‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left ((Psi n x).le_opNorm w) (norm_nonneg v)
      _ ≤ ‖v‖ * (‖x‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg w)) (norm_nonneg v)
      _ = ‖x‖ * ‖v‖ * ‖w‖ := by ring
  -- an ultrafilter refining `atTop`, and the limits along it
  have hU : ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) ≤ atTop :=
    Ultrafilter.of_le atTop
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hex : ∀ (x : A) (v w : H), ∃ z : ℂ,
      Tendsto (fun n ↦ ⟪v, Psi n x w⟫_ℂ) (U : Filter ℕ) (𝓝 z) := by
    intro x v w
    have hmem : ∀ n : ℕ,
        ⟪v, Psi n x w⟫_ℂ ∈ Metric.closedBall (0 : ℂ) (‖x‖ * ‖v‖ * ‖w‖) := by
      intro n
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hcoeff x v w n
    obtain ⟨z, -, hz⟩ :=
      (isCompact_closedBall (0 : ℂ) (‖x‖ * ‖v‖ * ‖w‖)).ultrafilter_le_nhds
        (U.map fun n ↦ ⟪v, Psi n x w⟫_ℂ)
        (by
          rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
          exact Filter.univ_mem' hmem)
    exact ⟨z, hz⟩
  choose L hL using hex
  -- the limit form is sesquilinear, linear in the algebra variable, and bounded
  have hLaddL : ∀ (x : A) (v v' w : H), L x (v + v') w = L x v w + L x v' w := by
    intro x v v' w
    refine eq_add_of_tendsto (hL x v w) (hL x v' w) (hL x (v + v') w) fun n ↦ ?_
    rw [inner_add_left]
  have hLsmulL : ∀ (x : A) (z : ℂ) (v w : H),
      L x (z • v) w = (starRingEnd ℂ) z * L x v w := by
    intro x z v w
    refine eq_const_mul_of_tendsto (hL x v w) (hL x (z • v) w) fun n ↦ ?_
    rw [inner_smul_left]
  have hLaddR : ∀ (x : A) (v w w' : H), L x v (w + w') = L x v w + L x v w' := by
    intro x v w w'
    refine eq_add_of_tendsto (hL x v w) (hL x v w') (hL x v (w + w')) fun n ↦ ?_
    rw [map_add, inner_add_right]
  have hLsmulR : ∀ (x : A) (z : ℂ) (v w : H), L x v (z • w) = z * L x v w := by
    intro x z v w
    refine eq_const_mul_of_tendsto (hL x v w) (hL x v (z • w)) fun n ↦ ?_
    rw [map_smul, inner_smul_right]
  have hLnorm : ∀ (x : A) (v w : H), ‖L x v w‖ ≤ ‖x‖ * ‖v‖ * ‖w‖ := by
    intro x v w
    refine le_of_tendsto (hL x v w).norm ?_
    exact Filter.Eventually.of_forall fun n ↦ hcoeff x v w n
  have hLxadd : ∀ (x x' : A) (v w : H), L (x + x') v w = L x v w + L x' v w := by
    intro x x' v w
    refine eq_add_of_tendsto (hL x v w) (hL x' v w) (hL (x + x') v w) fun n ↦ ?_
    rw [map_add, add_apply, inner_add_right]
  have hLxsmul : ∀ (z : ℂ) (x : A) (v w : H), L (z • x) v w = z * L x v w := by
    intro z x v w
    refine eq_const_mul_of_tendsto (hL x v w) (hL (z • x) v w) fun n ↦ ?_
    rw [map_smul, smul_apply, inner_smul_right]
  -- the form is the matrix of an operator, for each `x`
  have hop : ∀ x : A, ∃ T : H →L[ℂ] H, ∀ v w : H, ⟪v, T w⟫_ℂ = L x v w := fun x ↦
    exists_continuousLinearMap_of_sesq (L x) ‖x‖ (norm_nonneg x)
      (fun v v' w ↦ hLaddL x v v' w) (fun z v w ↦ hLsmulL x z v w)
      (fun v w w' ↦ hLaddR x v w w') (fun z v w ↦ hLsmulR x z v w)
      (fun v w ↦ hLnorm x v w)
  choose T hT using hop
  -- `x ↦ T x` is linear, since its coefficients are
  have hTadd : ∀ x x' : A, T (x + x') = T x + T x' := by
    intro x x'
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    rw [hT, hLxadd, add_apply, inner_add_right, hT, hT]
  have hTsmul : ∀ (z : ℂ) (x : A), T (z • x) = z • T x := by
    intro z x
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    rw [hT, hLxsmul, smul_apply, inner_smul_right, hT]
  -- form positivity passes to the limit
  have hcp : ∀ (m : ℕ) (a : Fin m → A) (v : Fin m → H),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, T (star (a i) * a j) (v j)⟫_ℂ).re := by
    intro m a v
    have hsum : Tendsto (fun n ↦ ∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, Psi n (star (a i) * a j) (v j)⟫_ℂ) (U : Filter ℕ)
        (𝓝 (∑ i : Fin m, ∑ j : Fin m,
          ⟪v i, T (star (a i) * a j) (v j)⟫_ℂ)) := by
      refine tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ ?_
      rw [hT]
      exact hL (star (a i) * a j) (v i) (v j)
    refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hsum) ?_
    exact Filter.Eventually.of_forall fun n ↦ hform n m a v
  -- unitality, and agreement on the subalgebra
  have hTone : T (1 : A) = 1 := by
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    show ⟪v, T (1 : A) w⟫_ℂ = ⟪v, w⟫_ℂ
    rw [hT]
    exact tendsto_nhds_unique (hL 1 v w) ((hone v w).mono_left hU)
  have hText : ∀ c : ↥C, T (c : A) = Φ c := by
    intro c
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    rw [hT]
    exact tendsto_nhds_unique (hL (c : A) v w) ((hCconv c v w).mono_left hU)
  exact ⟨{ toFun := T, map_add' := hTadd, map_smul' := hTsmul }, hcp, hTone, hText⟩

end

end CStarExactness
end GroupApproximation
