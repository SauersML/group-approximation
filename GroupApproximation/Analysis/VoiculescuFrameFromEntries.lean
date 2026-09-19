import GroupApproximation.Analysis.VoiculescuOneStep
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# (V3) From matrix entries to the frame

Glimm's lemma, run on the amplification `Mₙ(A) ⊆ B(Hⁿ)`, returns a unit vector of
`Hⁿ` — an `n`-tuple `ξ` of vectors of `H` — together with control on the *entries*
`⟪ξ_i, a ξ_j⟫`.  `Analysis/VoiculescuOneStep` asks instead for an operator bound,
`‖T⋆T - 1‖` and `‖T⋆aT - ρ(a)‖` small.  This module is the passage between the
two, and it mentions neither Glimm's lemma nor the amplification: it is finite-
dimensional linear algebra about an orthonormal basis.

## The bound, and why the constant does not matter

An operator on a finite-dimensional space whose entries in an orthonormal basis
are at most `d` has norm at most `n²d`, where `n` is the dimension: expand `Sx`
in the basis, bound each coefficient by `n·d·‖x‖` through Cauchy--Schwarz, and
sum.  The sharp constant is `n·d`, from the `ℓ²` rather than the `ℓ¹` norm of the
coefficient vector, and it is not worth the extra argument here — the frame
statement quantifies over every tolerance, so the amplification chooses `d` after
seeing `n`, and any constant depending only on `n` is absorbed.

## What is deliberately not here

The construction of the amplification, and the identification of its
compact-intersection hypothesis.  Everything below takes the `n`-tuple as given;
`frameOfTuple` builds the operator that carries the basis to it, and
`norm_sub_le_of_entries` converts entrywise control into operator control.  So
this module can be finished, and checked, before the amplification exists.

## The bound is not vacuous

`eq_zero_of_entries_eq_zero` is the model test: at `d = 0` the estimate says an
operator with vanishing entries vanishes, so the passage from entries to
operators loses nothing, and a statement proved through it is not weaker than the
entrywise one it came from.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι]
  {K₀ : Type*} [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Entries bound the operator -/

/-- **The entrywise bound.**  An operator whose entries in an orthonormal basis
are at most `d` has norm at most `n²d`. -/
theorem norm_le_of_entries (b : OrthonormalBasis ι ℂ K₀) (S : K₀ →L[ℂ] K₀)
    {d : ℝ} (hd : 0 ≤ d) (h : ∀ i j, ‖⟪b i, S (b j)⟫_ℂ‖ ≤ d) :
    ‖S‖ ≤ Fintype.card ι * (Fintype.card ι * d) := by
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hone : ∀ i, ‖b i‖ = 1 := fun i ↦ b.orthonormal.1 i
  have hcoef : ∀ j, ‖⟪b j, x⟫_ℂ‖ ≤ ‖x‖ := by
    intro j
    have := norm_inner_le_norm (𝕜 := ℂ) (b j) x
    rwa [hone j, one_mul] at this
  have hSx : S x = ∑ j, ⟪b j, x⟫_ℂ • S (b j) := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]
  have hcoord : ∀ i, ‖⟪b i, S x⟫_ℂ‖ ≤ Fintype.card ι * d * ‖x‖ := by
    intro i
    rw [hSx, inner_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.univ,
        ‖⟪b i, ⟪b j, x⟫_ℂ • S (b j)⟫_ℂ‖ ≤ d * ‖x‖ := by
      intro j _
      rw [inner_smul_right, norm_mul]
      calc ‖⟪b j, x⟫_ℂ‖ * ‖⟪b i, S (b j)⟫_ℂ‖
          ≤ ‖x‖ * d := mul_le_mul (hcoef j) (h i j) (norm_nonneg _) (norm_nonneg _)
        _ = d * ‖x‖ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (by ring)
  calc ‖S x‖ = ‖∑ i, ⟪b i, S x⟫_ℂ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, S x⟫_ℂ • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖⟪b i, S x⟫_ℂ‖ :=
        Finset.sum_congr rfl fun i _ ↦ by rw [norm_smul, hone i, mul_one]
    _ ≤ ∑ _i : ι, Fintype.card ι * d * ‖x‖ :=
        Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = Fintype.card ι * (Fintype.card ι * d) * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The difference of two operators is bounded by the difference of their
entries.  This is the form both clauses of the frame use: the Gram clause at
`R = 1`, the compression clause at `R = ρ(a)`. -/
theorem norm_sub_le_of_entries (b : OrthonormalBasis ι ℂ K₀) (S R : K₀ →L[ℂ] K₀)
    {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ i j, ‖⟪b i, S (b j)⟫_ℂ - ⟪b i, R (b j)⟫_ℂ‖ ≤ d) :
    ‖S - R‖ ≤ Fintype.card ι * (Fintype.card ι * d) := by
  refine norm_le_of_entries b (S - R) hd fun i j ↦ ?_
  have hentry : ⟪b i, (S - R) (b j)⟫_ℂ
      = ⟪b i, S (b j)⟫_ℂ - ⟪b i, R (b j)⟫_ℂ := by
    rw [_root_.sub_apply, inner_sub_right]
  rw [hentry]
  exact h i j

/-- **The model test.**  At `d = 0` the bound says an operator with vanishing
entries vanishes, so nothing is lost in passing from entries to operators. -/
theorem eq_zero_of_entries_eq_zero (b : OrthonormalBasis ι ℂ K₀) (S : K₀ →L[ℂ] K₀)
    (h : ∀ i j, ⟪b i, S (b j)⟫_ℂ = 0) : S = 0 := by
  have hle : ‖S‖ ≤ Fintype.card ι * (Fintype.card ι * (0:ℝ)) :=
    norm_le_of_entries b S le_rfl fun i j ↦ by rw [h i j]; simp
  rw [mul_zero, mul_zero] at hle
  exact norm_le_zero_iff.mp hle

/-! ## The frame carried by the tuple -/

/-- **The frame carried by a tuple.**  The operator sending `x` to
`∑ ⟪b i, x⟫ ξ_i`, written as a finite sum of rank-one maps rather than through
`Basis.constr` so that no finite-dimensionality of `K₀` is needed — only the
finiteness of the index. -/
def frameOfTuple (b : OrthonormalBasis ι ℂ K₀) (xi : ι → H) : K₀ →L[ℂ] H :=
  ∑ i, (innerSL ℂ (b i)).smulRight (xi i)

@[simp] theorem frameOfTuple_apply (b : OrthonormalBasis ι ℂ K₀) (xi : ι → H)
    (x : K₀) : frameOfTuple b xi x = ∑ i, ⟪b i, x⟫_ℂ • xi i := by
  simp [frameOfTuple]

/-- The frame carries the basis to the tuple. -/
theorem frameOfTuple_basis [DecidableEq ι] (b : OrthonormalBasis ι ℂ K₀)
    (xi : ι → H) (j : ι) : frameOfTuple b xi (b j) = xi j := by
  have hentry : ∀ i, ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 :=
    fun i ↦ orthonormal_iff_ite.mp b.orthonormal i j
  rw [frameOfTuple_apply]
  simp [hentry]

/-- The frame's range sits inside any submodule containing the tuple, which is
how the escape from the obstruction subspace is inherited. -/
theorem frameOfTuple_mem (b : OrthonormalBasis ι ℂ K₀) (xi : ι → H)
    (V : Submodule ℂ H) (hxi : ∀ i, xi i ∈ V) (x : K₀) :
    frameOfTuple b xi x ∈ V := by
  rw [frameOfTuple_apply]
  exact Submodule.sum_mem V fun i _ ↦ Submodule.smul_mem V _ (hxi i)

/-! ## Reading the entries of a compression -/

/-- The entries of a compression are the inner products the amplified Glimm
lemma controls. -/
theorem inner_compress_entry [CompleteSpace K₀] [CompleteSpace H]
    (b : OrthonormalBasis ι ℂ K₀)
    (T : K₀ →L[ℂ] H) (y : H →L[ℂ] H) (i j : ι) :
    ⟪b i, (ContinuousLinearMap.adjoint T ∘L y ∘L T) (b j)⟫_ℂ
      = ⟪T (b i), y (T (b j))⟫_ℂ := by
  simpa using ContinuousLinearMap.adjoint_inner_right T (b i) (y (T (b j)))

/-- The entries of a Gram operator are the inner products of the tuple. -/
theorem inner_gram_entry [CompleteSpace K₀] [CompleteSpace H]
    (b : OrthonormalBasis ι ℂ K₀)
    (T : K₀ →L[ℂ] H) (i j : ι) :
    ⟪b i, (ContinuousLinearMap.adjoint T ∘L T) (b j)⟫_ℂ
      = ⟪T (b i), T (b j)⟫_ℂ := by
  simpa using ContinuousLinearMap.adjoint_inner_right T (b i) (T (b j))

/-- The entries of the identity are the Kronecker delta. -/
theorem inner_one_entry [DecidableEq ι] (b : OrthonormalBasis ι ℂ K₀) (i j : ι) :
    ⟪b i, (1 : K₀ →L[ℂ] K₀) (b j)⟫_ℂ = if i = j then 1 else 0 := by
  have h1 : (1 : K₀ →L[ℂ] K₀) (b j) = b j := rfl
  rw [h1]
  exact orthonormal_iff_ite.mp b.orthonormal i j

/-- **The bridge, assembled.**  From entrywise control of an `n`-tuple — almost
orthonormality, and almost reproducing a prescribed operator against one element
of `B(H)` — the frame it carries satisfies the two operator bounds the frame
statement of `Analysis/VoiculescuOneStep` asks for, and escapes the obstruction
subspace.  This is everything between the amplified Glimm lemma's output and
`FrameApproximationStatement` except the choice of tolerance.

`K₀` is not asked to be finite-dimensional: the finiteness of the index is what
the estimate uses. -/
theorem frame_bounds_of_entries [DecidableEq ι] [CompleteSpace K₀] [CompleteSpace H]
    (b : OrthonormalBasis ι ℂ K₀) (xi : ι → H) (V : Submodule ℂ H)
    (hxi : ∀ i, xi i ∈ V) {d : ℝ} (hd : 0 ≤ d)
    (hgram : ∀ i j, ‖⟪xi i, xi j⟫_ℂ - (if i = j then 1 else 0)‖ ≤ d)
    (y : H →L[ℂ] H) (R : K₀ →L[ℂ] K₀)
    (hy : ∀ i j, ‖⟪xi i, y (xi j)⟫_ℂ - ⟪b i, R (b j)⟫_ℂ‖ ≤ d) :
    (∀ x, frameOfTuple b xi x ∈ V) ∧
      ‖ContinuousLinearMap.adjoint (frameOfTuple b xi) ∘L frameOfTuple b xi - 1‖
        ≤ Fintype.card ι * (Fintype.card ι * d) ∧
      ‖ContinuousLinearMap.adjoint (frameOfTuple b xi) ∘L y ∘L frameOfTuple b xi
          - R‖ ≤ Fintype.card ι * (Fintype.card ι * d) := by
  refine ⟨frameOfTuple_mem b xi V hxi, ?_, ?_⟩
  · refine norm_sub_le_of_entries b _ 1 hd fun i j ↦ ?_
    rw [inner_gram_entry b (frameOfTuple b xi) i j, inner_one_entry b i j,
      frameOfTuple_basis b xi i, frameOfTuple_basis b xi j]
    exact hgram i j
  · refine norm_sub_le_of_entries b _ R hd fun i j ↦ ?_
    rw [inner_compress_entry b (frameOfTuple b xi) y i j,
      frameOfTuple_basis b xi i, frameOfTuple_basis b xi j]
    exact hy i j


end

end ShulmanFill
end GroupApproximation
