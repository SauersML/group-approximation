import GroupApproximation.GGT.DGOUniformSumBoundComponent

/-!
# Both conclusions of DGO Proposition 4.14 for additive quasi-geodesics

The completed balanced surgery supplies one constant uniform in the polygon
side count. The component-collapse and recutting argument provides the
individual-component clause with the same constant, enlarged by a factor
of three. The multiplicative constant is one; the additive error is any real.
The general multiplicative-parameter theorem remains separate.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The uniform sum and individual-component conclusions of Proposition
4.14 at multiplicative constant one, with their original geometric inputs. -/
theorem exists_uniform414_one
    (D : RelGenSet G Lambda)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (hbase : DGO421BaseSymmetric D) (c : ℝ) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 c C ∧
      ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
        IsQuasiGeodesicPolygon D 1 c n v word →
        ∀ (lam : Lambda) (i k : ℕ), IsComp lam word i k →
          IsIsolated D.fam lam v word i →
            (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall lam (C * n) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniformSumBound_one_of_hyperbolic D hhyp hbase c
  refine ⟨3 * C, by omega, hbound.mono_radius (by omega), ?_⟩
  exact hbound.component_span

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniform414_one
