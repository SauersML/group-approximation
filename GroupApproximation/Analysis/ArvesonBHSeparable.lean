import GroupApproximation.Analysis.ArvesonIsometryFamily
import GroupApproximation.Analysis.ArvesonLimitStep

/-!
# Arveson's extension theorem at a `B(H)` target, with nothing left as data

`Analysis/ArvesonBHTarget.arvesonBH_of_limit` proved the theorem from three
inputs: the matrix case, the limit step, and an exhausting family of isometries
supplied by the caller.  The limit step is discharged in
`Analysis/ArvesonLimitStep`, and `Analysis/ArvesonIsometryFamily` builds the
isometry attached to a finite-dimensional subspace.  This module assembles the
family for a separable `H` and spends both, leaving Arveson at a `B(H)` target
with no hypothesis beyond separability of the space — which is where it was
always going to be needed, since a non-separable `H` has no exhausting sequence
of finite-dimensional subspaces at all.

The family is the one (V1a) already uses for a different purpose: the spans of
the prefixes of a dense sequence, whose orthogonal projections converge
strongly to the identity.  Reading the two weak convergences off that strong
one is the whole of the assembly, and the second of them — the compression
`Pₙ T Pₙ → T` — is where the uniform bound is spent, since there the outer
projection meets a moving vector.
-/

namespace GroupApproximation
namespace CStarExactness

open Filter Topology

open scoped InnerProductSpace

noncomputable section

/-- **The exhausting family exists on a separable space.**  Indices, isometries,
and the four clauses `arvesonBH_of_limit` consumes. -/
theorem exists_exhausting_isometry_family (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    ∃ (k : ℕ → ℕ) (J : ∀ n, EuclideanSpace ℂ (Fin (k n)) →L[ℂ] H),
      (∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin (k n))),
        ContinuousLinearMap.adjoint (J n) (J n v) = v) ∧
      (∀ n : ℕ, ‖J n‖ ≤ 1) ∧
      (∀ v w : H, Tendsto (fun n ↦
        ⟪v, ((J n).comp (ContinuousLinearMap.adjoint (J n))) w⟫_ℂ)
        atTop (𝓝 ⟪v, w⟫_ℂ)) ∧
      (∀ (T : H →L[ℂ] H) (v w : H), Tendsto (fun n ↦
        ⟪v, (J n) ((ContinuousLinearMap.adjoint (J n))
          (T ((J n) ((ContinuousLinearMap.adjoint (J n)) w))))⟫_ℂ)
        atTop (𝓝 ⟪v, T w⟫_ℂ)) := by
  haveI : Nonempty H := ⟨0⟩
  have hdense : DenseRange (TopologicalSpace.denseSeq H) :=
    TopologicalSpace.denseRange_denseSeq H
  have hproj : ∀ x : H, Tendsto (fun n ↦
      (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection x)
      atTop (𝓝 x) := fun x ↦
    ShulmanFill.tendsto_starProjection_densePrefixSpan _ hdense x
  have hpnorm : ∀ n : ℕ,
      ‖(ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection‖ ≤ 1 :=
    fun n ↦ Submodule.starProjection_norm_le _
  have hJP : ∀ (n : ℕ) (x : H),
      subspaceIsometry (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n)
        (ContinuousLinearMap.adjoint (subspaceIsometry
          (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n)) x)
        = (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection x :=
    fun n x ↦ subspaceIsometry_adjoint_apply _ x
  refine ⟨fun n ↦ Module.finrank ℂ
      (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n),
    fun n ↦ subspaceIsometry
      (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n),
    fun n v ↦ adjoint_subspaceIsometry_apply _ v,
    fun n ↦ norm_subspaceIsometry_le _, ?_, ?_⟩
  · intro v w
    have h : Tendsto (fun n ↦
        ⟪v, (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection w⟫_ℂ)
        atTop (𝓝 ⟪v, w⟫_ℂ) := tendsto_const_nhds.inner (hproj w)
    refine h.congr fun n ↦ ?_
    rw [← hJP n w]
    rfl
  · intro T v w
    have h : Tendsto (fun n ↦
        ⟪v, (ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection
          (T ((ShulmanFill.densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection
            w))⟫_ℂ) atTop (𝓝 ⟪v, T w⟫_ℂ) :=
      tendsto_const_nhds.inner (tendsto_compress _ hpnorm hproj T w)
    refine h.congr fun n ↦ ?_
    rw [hJP n w, hJP n (T _)]

/-- **Arveson's extension theorem at a `B(H)` target, unconditionally.**  For a
separable `H`, a unital form-positive map on a closed `⋆`-subalgebra extends to
one on the whole algebra.  Nothing is left as data: the limit step and the
exhausting family are both supplied. -/
theorem arvesonBH_of_separable {A : Type} [CStarAlgebra A] {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (C : StarSubalgebra ℂ A) (hC : IsClosed (C : Set A))
    (Φ : ↥C →ₗ[ℂ] (H →L[ℂ] H)) (hform : IsFormCP Φ)
    (hstar : ∀ c : ↥C, Φ (star c) = star (Φ c)) (hone : Φ 1 = 1) :
    ∃ Ψ : A →ₗ[ℂ] (H →L[ℂ] H), IsFormCP Ψ ∧ Ψ 1 = 1 ∧
      ∀ c : ↥C, Ψ (c : A) = Φ c := by
  obtain ⟨k, J, hJ, hJnorm, hWOTone, hWOTcompress⟩ :=
    exists_exhausting_isometry_family H
  refine arvesonBH_of_limit arvesonLimit C hC Φ hform hstar hone k J hJ hJnorm
    hWOTone ?_
  intro c v w
  refine (hWOTcompress (Φ c) v w).congr fun n ↦ ?_
  rw [isometryCompress_apply]

end

end CStarExactness
end GroupApproximation
