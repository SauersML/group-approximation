import GroupApproximation.GGT.DGOTheorem442ProjectionAxiomA4

/-!
# The projection system produced in DGO Theorem 4.42

This file packages the four projection axioms of DGO Definition 4.1 together
with equivariance.  The projection functions are real-valued, with
nonnegativity recorded explicitly in place of using `ℝ≥0` as their codomain.

The (A3) and (A4) proofs naturally produce different valid thresholds.  Their
maximum is one common `ξ`, exactly as allowed by the definition: increasing the
threshold preserves (A3), and the new (A4) large-projection set is a subset of
the old one.
-/

namespace GroupApproximation
namespace GGT

universe u v

/-- DGO's axioms (A1)--(A4) for a family of projection distances.  Arguments
which occur in the source only off the diagonal carry the corresponding
inequality hypotheses. -/
structure ProjectionSystem (V : Type u) where
  projDist : V → V → V → ℝ
  ξ : ℝ
  ξ_pos : 0 < ξ
  nonneg : ∀ Y A B, 0 ≤ projDist Y A B
  comm : ∀ Y A B, projDist Y A B = projDist Y B A
  triangle : ∀ Y A B C, Y ≠ A → Y ≠ B → Y ≠ C →
    projDist Y A C ≤ projDist Y A B + projDist Y B C
  behrstock : ∀ Y A B, Y ≠ A → Y ≠ B → A ≠ B →
    min (projDist Y A B) (projDist B A Y) < ξ
  finite_large : ∀ A B, A ≠ B → {Y | ξ ≤ projDist Y A B}.Finite

namespace ProjectionSystem

variable {V : Type u}

/-- Vertices with projection of `(A,B)` at least the system threshold. -/
def largeSet (P : ProjectionSystem V) (A B : V) : Set V :=
  {Y | P.ξ ≤ P.projDist Y A B}

theorem largeSet_finite (P : ProjectionSystem V) {A B : V} (hAB : A ≠ B) :
    (P.largeSet A B).Finite :=
  P.finite_large A B hAB

end ProjectionSystem

/-- A projection system preserved by an action, as in the paragraph following
DGO Definition 4.1. -/
structure EquivariantProjectionSystem (G : Type u) (V : Type v)
    [Group G] [MulAction G V] extends ProjectionSystem V where
  smul_projDist : ∀ (g : G) (Y A B : V),
    projDist (g • Y) (g • A) (g • B) = projDist Y A B

namespace Elementary

open GroupApproximation.HullGeometry

universe w

variable {G : Type u} [Group G] {S : Type w} [PseudoMetricSpace S]
  [MulAction G S]

/-- The approximate coset-orbit projection distances, with all four DGO
axioms and simultaneous-left-translation equivariance assembled into one
projection system. -/
noncomputable def approxCosetEquivariantProjectionSystem
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    EquivariantProjectionSystem G (G ⧸ H) := by
  let a3 :=
    exists_approxCosetProjectionDistance_min_lt
      hδ hδ0 hδpos hgeo hiso hqc hsep
  let ξ₃ : ℝ := Classical.choose a3
  have hA3spec := Classical.choose_spec a3
  have hξ₃ : 0 < ξ₃ := hA3spec.1
  have hA3 := hA3spec.2
  let a4 :=
    exists_approxCosetProjectionDistance_ge_finite
      hδ hδ0 hδpos hgeo hiso hqc hsep
  let ξ₄ : ℝ := Classical.choose a4
  have hA4spec := Classical.choose_spec a4
  have hξ₄ : 0 < ξ₄ := hA4spec.1
  have hA4 := hA4spec.2
  let ξ : ℝ := max ξ₃ ξ₄
  refine
    { projDist := approxCosetProjectionDistance H s δ
      ξ := ξ
      ξ_pos := lt_of_lt_of_le hξ₃ (le_max_left _ _)
      nonneg := fun _ _ _ => Metric.diam_nonneg
      comm := approxCosetProjectionDistance_comm H s δ
      triangle := ?_
      behrstock := ?_
      finite_large := ?_
      smul_projDist := fun g Y A B =>
        approxCosetProjectionDistance_smul hiso H s g δ Y A B }
  · intro Y A B C hYA hYB hYC
    exact approxCosetProjectionDistance_triangle
      hδ hδ0 hδpos hgeo hiso hqc hsep Y A B C hYA hYB hYC
  · intro Y A B hYA hYB hAB
    exact (hA3 Y A B hYA hYB hAB).trans_le (le_max_left _ _)
  · intro A B hAB
    exact (hA4 A B hAB).subset fun _ hlarge =>
      (le_max_right ξ₃ ξ₄).trans hlarge

end Elementary
end GGT
end GroupApproximation
