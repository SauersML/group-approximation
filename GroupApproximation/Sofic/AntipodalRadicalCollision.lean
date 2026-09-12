import GroupApproximation.Sofic.AntipodalTraceExtraction
import GroupApproximation.Sofic.CliffordPhaseExtraction
import GroupApproximation.Sofic.HyperlinearResidualDetector
import GroupApproximation.Sofic.HyperlinearUltraproductBridge

/-!
# The antipodal radical-collision endpoint

This file packages the exact endpoint of the antipodal program.  An
asymptotic unitary representation need not be faithful.  If one marked
element admits asymptotically antipodal conjugators, however, the induced
tracial-ultraproduct homomorphism detects that element.  When the element is
in the full sofic residual, the range is therefore hyperlinear and nonsofic.

The only hypothesis not supplied by the existing candidate constructions is
the antipodal profile itself.
-/

namespace GroupApproximation

open Filter Matrix

variable {G : Type} [Group G]

/-- An asymptotically antipodal coordinate profile detects its marked element
in the induced tracial matrix ultraproduct. -/
theorem AsymptoticUnitaryRepresentation.antipodal_detects
    (A : AsymptoticUnitaryRepresentation G) (x : G)
    (S : ∀ n, Matrix.unitaryGroup (A.model n) ℂ)
    (hanti : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsNormSq (A.model n)
        ((S n : Matrix (A.model n) (A.model n) ℂ)
          * A.map n x * (S n : Matrix (A.model n) (A.model n) ℂ)ᴴ
          + A.map n x) ≤ ε)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    A.toUltraproductHom hcof x ≠ 1 := by
  intro htrivial
  have heq :
      (1 : UniversalHyperlinear 𝒰 A.model A.modelNonempty) =
        QuotientGroup.mk (fun n ↦ A.map n x) := by
    rw [← A.toUltraproductHom_apply hcof x]
    exact htrivial.symm
  have hmem : (fun n ↦ A.map n x) ∈
      nullUnitarySubgroup 𝒰 A.model A.modelNonempty := by
    have h := QuotientGroup.eq.mp heq
    simpa only [inv_one, one_mul] using h
  have hclose : ∀ᶠ n in (𝒰 : Filter ℕ),
      hsLengthSq (A.model n) (A.map n x) < 1 := hmem 1 (by norm_num)
  obtain ⟨N, hN⟩ := hanti 1 (by norm_num)
  have hfar : ∀ᶠ n in (𝒰 : Filter ℕ),
      1 ≤ hsLengthSq (A.model n) (A.map n x) :=
    eventually_of_atTop hcof N (fun n hn ↦ by
      change 1 ≤ hsDistSq (A.model n) (A.map n x) 1
      exact one_le_hsDistSq_one_of_antipodalDefect_le_one
        (A.model n) (S n).2 (A.map n x).2 (A.modelNonempty n) (hN n hn))
  obtain ⟨n, hnfar, hnclose⟩ := (hfar.and hclose).exists
  linarith

/-- Convergence of a marked word to the scalar `-1` detects that word in the
induced tracial matrix ultraproduct. -/
theorem AsymptoticUnitaryRepresentation.negOnePhase_detects
    (A : AsymptoticUnitaryRepresentation G) (x : G)
    (hphase : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (A.model n) (A.map n x) (-1) ≤ ε)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    A.toUltraproductHom hcof x ≠ 1 := by
  intro htrivial
  have heq :
      (1 : UniversalHyperlinear 𝒰 A.model A.modelNonempty) =
        QuotientGroup.mk (fun n ↦ A.map n x) := by
    rw [← A.toUltraproductHom_apply hcof x]
    exact htrivial.symm
  have hmem : (fun n ↦ A.map n x) ∈
      nullUnitarySubgroup 𝒰 A.model A.modelNonempty := by
    have h := QuotientGroup.eq.mp heq
    simpa only [inv_one, one_mul] using h
  have hclose : ∀ᶠ n in (𝒰 : Filter ℕ),
      hsLengthSq (A.model n) (A.map n x) < 1 := hmem 1 (by norm_num)
  obtain ⟨N, hN⟩ := hphase 1 (by norm_num)
  have hfar : ∀ᶠ n in (𝒰 : Filter ℕ),
      1 ≤ hsLengthSq (A.model n) (A.map n x) :=
    eventually_of_atTop hcof N (fun n hn ↦ by
      change 1 ≤ hsDistSq (A.model n) (A.map n x) 1
      exact one_le_hsDistSq_one_of_negOneDefect_le_one
        (A.model n) (A.map n x).2 (A.modelNonempty n) (hN n hn))
  obtain ⟨n, hnfar, hnclose⟩ := (hfar.and hclose).exists
  linarith

/-- **Antipodal radical collision.**  A sofic-residual element with one
asymptotically antipodal unitary model produces a hyperlinear nonsofic range. -/
theorem exists_hyperlinear_not_isSofic_of_antipodal_soficInvisible
    (A : AsymptoticUnitaryRepresentation G) {x : G}
    (hx : SoficInvisible x)
    (S : ∀ n, Matrix.unitaryGroup (A.model n) ℂ)
    (hanti : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsNormSq (A.model n)
        ((S n : Matrix (A.model n) (A.model n) ℂ)
          * A.map n x * (S n : Matrix (A.model n) (A.model n) ℂ)ᴴ
          + A.map n x) ≤ ε) :
    ∃ (Q : Type) (_ : Group Q), IsHyperlinear Q ∧ ¬IsSofic Q := by
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((𝒰 : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let rho := A.toUltraproductHom hcof
  have hdetect : rho x ≠ 1 := A.antipodal_detects x S hanti hcof
  have hrange : IsHyperlinear rho.range :=
    isHyperlinear_of_hyperlinearUltraproductEmbedding
      𝒰 A.model A.modelNonempty rho.range.subtype Subtype.val_injective
  exact ⟨rho.range, inferInstance, hrange,
    not_isSofic_range_of_soficInvisible hx rho hdetect⟩

/-- **Scalar-phase radical collision.**  A sofic-residual element that tends
to the scalar `-1` in one asymptotic unitary representation produces a
hyperlinear nonsofic range. -/
theorem exists_hyperlinear_not_isSofic_of_negOnePhase_soficInvisible
    (A : AsymptoticUnitaryRepresentation G) {x : G}
    (hx : SoficInvisible x)
    (hphase : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (A.model n) (A.map n x) (-1) ≤ ε) :
    ∃ (Q : Type) (_ : Group Q), IsHyperlinear Q ∧ ¬IsSofic Q := by
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((𝒰 : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let rho := A.toUltraproductHom hcof
  have hdetect : rho x ≠ 1 := A.negOnePhase_detects x hphase hcof
  have hrange : IsHyperlinear rho.range :=
    isHyperlinear_of_hyperlinearUltraproductEmbedding
      𝒰 A.model A.modelNonempty rho.range.subtype Subtype.val_injective
  exact ⟨rho.range, inferInstance, hrange,
    not_isSofic_range_of_soficInvisible hx rho hdetect⟩

end GroupApproximation
