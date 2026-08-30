import GroupApproximation.Analysis.VoiculescuProjectionAssembly
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The exhausting family of isometries a `B(H)` target needs

`Analysis/ArvesonBHTarget.arvesonBH_of_limit` proves Arveson's extension
theorem at a `B(H)` target from an *exhausting family of isometries*
`Jₙ : ℂ^{kₙ} → H`, taken there as data: the module says so, on the ground that
in the printed setting `H = ℓ²` and `Jₙ` is the inclusion of the first `kₙ`
coordinates.  For a separable `H` the family exists, and this module builds it,
so that the theorem applies with no data hypothesis left.

The pieces are already in the tree.  (V1a) produced, for a separable `H`, the
finite-dimensional subspaces `densePrefixSpan d n` — the spans of the prefixes
of a dense sequence — and proved that their orthogonal projections converge
strongly to the identity.  What remains is to turn each finite-dimensional
subspace into an isometry from a coordinate space, which is what an orthonormal
basis is, and to read the two weak convergences off the strong one.

## The identity that does the work

`Jₙ Jₙ⋆` is the orthogonal projection onto the subspace.  That is proved here
from the characterisation of the projection rather than from idempotence: `J J⋆x`
lies in the subspace because `J` maps into it, and `x - J J⋆x` is orthogonal to
it because every element of the subspace is `J u` and
`⟪x - J J⋆x, J u⟫ = ⟪J⋆x, u⟫ - ⟪J⋆x, u⟫`, using `J⋆J = 1` once.  With that,
both convergence hypotheses of `arvesonBH_of_limit` are statements about
`starProjection`, and (V1a) has them.

The second of them is the compression `Pₙ T Pₙ → T`, which is not quite the
strong convergence: it needs the uniform bound as well, since the outer `Pₙ`
is applied to a *moving* vector.  That step is isolated below as
`tendsto_compress`, stated for an arbitrary strongly convergent family of
contractions, because it is a fact about approximate units and not about
projections.
-/

namespace GroupApproximation
namespace CStarExactness

open Filter Topology

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The isometry attached to a finite-dimensional subspace -/

/-- **The coordinate isometry of a finite-dimensional subspace**: the standard
orthonormal basis of `V`, read as a map from `ℂ^{dim V}` into `H`. -/
def subspaceIsometry (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] H :=
  V.subtypeL.comp
    ((stdOrthonormalBasis ℂ V).repr.symm.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace H] in
theorem subspaceIsometry_apply (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (v : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    subspaceIsometry V v = (((stdOrthonormalBasis ℂ V).repr.symm v : V) : H) := rfl

omit [CompleteSpace H] in
theorem subspaceIsometry_mem (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (v : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) : subspaceIsometry V v ∈ V :=
  Submodule.coe_mem _

omit [CompleteSpace H] in
theorem norm_subspaceIsometry_apply (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (v : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    ‖subspaceIsometry V v‖ = ‖v‖ := by
  show ‖((stdOrthonormalBasis ℂ V).repr.symm v : V)‖ = ‖v‖
  exact (stdOrthonormalBasis ℂ V).repr.symm.norm_map v

omit [CompleteSpace H] in
theorem norm_subspaceIsometry_le (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    ‖subspaceIsometry V‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  rw [norm_subspaceIsometry_apply, one_mul]

omit [CompleteSpace H] in
/-- Every element of the subspace is hit, which is what makes `J J⋆` the
projection rather than merely a positive contraction. -/
theorem subspaceIsometry_surjOn (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    {w : H} (hw : w ∈ V) : ∃ v, subspaceIsometry V v = w := by
  refine ⟨(stdOrthonormalBasis ℂ V).repr ⟨w, hw⟩, ?_⟩
  show (((stdOrthonormalBasis ℂ V).repr.symm
    ((stdOrthonormalBasis ℂ V).repr ⟨w, hw⟩) : V) : H) = w
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem adjoint_comp_subspaceIsometry (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    ContinuousLinearMap.adjoint (subspaceIsometry V) ∘L subspaceIsometry V = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (norm_subspaceIsometry_apply V)

theorem adjoint_subspaceIsometry_apply (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (v : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    ContinuousLinearMap.adjoint (subspaceIsometry V) (subspaceIsometry V v) = v := by
  have h := adjoint_comp_subspaceIsometry V
  calc ContinuousLinearMap.adjoint (subspaceIsometry V) (subspaceIsometry V v)
      = (ContinuousLinearMap.adjoint (subspaceIsometry V) ∘L subspaceIsometry V) v := rfl
    _ = (1 : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) v := by rw [h]
    _ = v := rfl

/-- **`J J⋆` is the orthogonal projection.**  Proved from the characterisation
of the projection, so no idempotence calculation appears. -/
theorem subspaceIsometry_adjoint_apply (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (x : H) :
    subspaceIsometry V (ContinuousLinearMap.adjoint (subspaceIsometry V) x)
      = V.starProjection x := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (subspaceIsometry_mem V _)
    fun w hw ↦ ?_).symm
  obtain ⟨u, rfl⟩ := subspaceIsometry_surjOn V hw
  rw [inner_sub_left]
  have h1 : ⟪x, subspaceIsometry V u⟫_ℂ
      = ⟪ContinuousLinearMap.adjoint (subspaceIsometry V) x, u⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_left (subspaceIsometry V) u x).symm
  have h2 : ⟪subspaceIsometry V (ContinuousLinearMap.adjoint (subspaceIsometry V) x),
      subspaceIsometry V u⟫_ℂ
      = ⟪ContinuousLinearMap.adjoint (subspaceIsometry V) x, u⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_subspaceIsometry_apply]
  rw [h1, h2, sub_self]

/-! ## The compression converges -/

omit [CompleteSpace H] in
/-- **A strongly convergent family of contractions compresses to the identity.**
The outer factor is applied to a moving vector, so the uniform bound is needed
as well as the strong convergence; this is the only place either is used. -/
theorem tendsto_compress (P : ℕ → (H →L[ℂ] H)) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x : H, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (T : H →L[ℂ] H) (w : H) :
    Tendsto (fun n ↦ P n (T (P n w))) atTop (𝓝 (T w)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun n ↦ ‖T‖ * ‖P n w - w‖ + ‖P n (T w) - T w‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ ‖P n w - w‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hstrong w)
    have h2 : Tendsto (fun n ↦ ‖P n (T w) - T w‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hstrong (T w))
    have h := (h1.const_mul ‖T‖).add h2
    simpa using h
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  have hsplit : P n (T (P n w)) - T w
      = P n (T (P n w) - T w) + (P n (T w) - T w) := by
    rw [map_sub]
    abel
  have hfirst : ‖P n (T (P n w) - T w)‖ ≤ ‖T‖ * ‖P n w - w‖ := by
    refine le_trans ((P n).le_opNorm _) ?_
    have hb : ‖P n‖ * ‖T (P n w) - T w‖ ≤ ‖T (P n w) - T w‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (hP n)
    refine le_trans hb ?_
    have : T (P n w) - T w = T (P n w - w) := by rw [map_sub]
    rw [this]
    exact (T).le_opNorm _
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add_left hfirst _)

end

end CStarExactness
end GroupApproximation
