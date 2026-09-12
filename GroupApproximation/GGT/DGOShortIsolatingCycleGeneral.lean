import GroupApproximation.GGT.DGOShortIsolatingCycleGeneralUnit

/-!
# The short isolating cycle at general quasi-geodesic parameters

The original `ExistsShortIsolatingCycleAt` interface is now discharged.
Collapse the exempt side, run the proved unit-component case tree, and
compose the span identities. The cycle length is uniform in the polygon.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The general-parameter short isolating-cycle conclusion used in DGO's
Lemma 4.16 construction, with the original interface unchanged. -/
theorem existsShortIsolatingCycleAt
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (mu : ℝ) (b δ : ℕ) (hmu : 0 < mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ExistsShortIsolatingCycleAt D mu b := by
  obtain ⟨L, hL⟩ := exists_short_isolating_cycleAt_of_unit D hsymm mu b δ hmu hδ
  refine ⟨L, ?_⟩
  intro lam v w c hQ hcomp hiso
  obtain ⟨w', c', hQ', hc1, hcomp', hiso', hspan⟩ :=
    hQ.exists_unit_side_zero D hcomp hiso
  obtain ⟨q, hlet, hclosed, hlength, hqcomp, hqiso, hqspan⟩ :=
    hL lam v w' c' hQ' hc1 hcomp' hiso'
  exact ⟨v, q, hlet, hclosed, hlength, hqcomp, hqiso, hqspan.trans hspan⟩

/-- The resulting uniform relative-radius bound for the distinguished
component of a general quasi-geodesic four-gon. -/
theorem exists_isolatedComponentBound_quasiGeodesicFourGon
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (mu : ℝ) (b δ : ℕ) (hmu : 0 < mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, ∀ (lam : Lambda) (v : G) (w : List (RelLetter G Lambda)) (c : ℕ → ℕ),
      QuasiGeodesicFourGon D mu b v w c →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam C := by
  obtain ⟨C, hC⟩ := existsShortIsolatingCycleAt D hsymm mu b δ hmu hδ
  refine ⟨C, ?_⟩
  intro lam v w c hQ hcomp hiso
  obtain ⟨u, q, hlet, hclosed, hlength, hqcomp, hqiso, hspan⟩ := hC lam v w c hQ hcomp hiso
  have hball := relBall_of_isolated_of_closed D hsymm lam u hlet hclosed hqcomp hqiso
  rw [hspan] at hball
  exact relBall_mono_radius D lam hlength hball

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.existsShortIsolatingCycleAt
#audit_axioms GroupApproximation.GGT.OsinComponents.exists_isolatedComponentBound_quasiGeodesicFourGon
