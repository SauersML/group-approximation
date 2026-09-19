import GroupApproximation.GGT.DGOProposition414GeneralLinear
import GroupApproximation.GGT.DGOUniformSumBoundComponent
import GroupApproximation.GGT.DGOLemma421FromUniform414

/-!
# DGO Proposition 4.14 and Lemma 4.21(b), with their original propositions

The general balanced-surgery proof gives a constant uniform in polygon size.
Rounding the additive error handles every real parameter. Component collapse
and recutting give the individual bound with the same enlarged constant.
The complete consecutive-component proof then discharges Lemma 4.21(b).
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- The uniform sum bound under the original hyperbolicity hypothesis, at
every multiplicative constant at least one and every real additive error. -/
theorem exists_uniformSumBound_general_of_hyperbolic
    (D : RelGenSet G Λ)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (hbase : DGO421BaseSymmetric D) (mu c : ℝ) (hmu : 1 ≤ mu) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D mu c C := by
  obtain ⟨delta, hdelta⟩ := hhyp
  obtain ⟨C, hC, hbound⟩ := exists_uniformSumBound_general D hbase mu ⌈c⌉₊ hmu
    (isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdelta)
  exact ⟨C, hC, hbound.of_error_le (Nat.le_ceil c)⟩

end GroupApproximation.GGT.DGOProposition414

namespace GroupApproximation.GGT.OsinComponents

universe u w

/-- Dahmani--Guirardel--Osin Proposition 4.14, with the original quantifier
order and both conclusions, without any unproved geometric inputs. -/
theorem dgoProposition414Uniform : DGOProposition414Uniform.{u, w} := by
  intro G _ Λ D hhyp hbase mu c hmu _hc
  obtain ⟨C, hC, hbound⟩ :=
    DGOProposition414.exists_uniformSumBound_general_of_hyperbolic D hhyp hbase mu c hmu
  exact ⟨3 * C, by omega, hbound.mono_radius (by omega), hbound.component_span⟩

/-- The original full Lemma 4.21(b), including consecutive maximal
components, both separators, and the two path basepoints. -/
theorem dgoLemma421b : DGOLemma421b.{u, w} :=
  dgoLemma421b_of_uniform414 dgoProposition414Uniform

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniformSumBound_general_of_hyperbolic
#audit_closed_axioms GroupApproximation.GGT.OsinComponents.dgoProposition414Uniform
#audit_closed_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421b
