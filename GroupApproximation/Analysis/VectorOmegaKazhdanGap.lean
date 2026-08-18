import GroupApproximation.Analysis.VectorOmegaAction
import GroupApproximation.Analysis.AbstractSpectralGap
import GroupApproximation.Sofic.UltraproductKazhdanProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The Kazhdan spectral gap on `H_ω`

`\label{thm:normal-kazhdan}` continues, immediately after forming the
representation:

> for `h = card(S)⁻¹ Σ_{a∈S} π(a)` the Kazhdan pair puts `sp(h)` in
> `[−1, θ] ∪ {1}` with `θ = 1 − ε₀²/(4·card S)`.

That sentence is ledger row `NK.05`, and both of its clauses now have the
printed objects underneath them.

## What was already there, and what was missing

The *estimate* has been formalized for some time, and with the manuscript's own
constant: `AbstractSpectralGap.unitaryAverage_spectrum_le` says that for a
Kazhdan pair `(Q, ε)` and a unitary representation of the group in **any**
unital C*-algebra, every real spectral value of the unitary average over a
finite symmetric `S ⊇ Q` containing `1`, other than `1` itself, is at most
`1 − ε²/(4·card S)`.  It was built for the strict-Kazhdan-compression lane and
proved through `SpectralStateWitness` and `GNSEigenvector`.

What was missing is the sentence's subject.  `NK.05` is not about an arbitrary
C*-algebra: it is about the average of `π(a) = [V_{a,n}]_ω` acting on the
Hilbert-space ultraproduct of the coordinate spaces, and until
`Analysis/VectorHilbertUltraproduct.lean`,
`Analysis/VectorHilbertComplete.lean` and `Analysis/VectorOmegaAction.lean`
there was no such object in the development to be about — which is why the
ledger cites a declaration performing the cut at a finite stage instead, over
substituted objects.

This file supplies the application.  `B(H_ω)` is a unital C*-algebra because
`H_ω` is a Hilbert space, `π` lands in its unitary group because a
coordinatewise unitary class acts by a surjective isometry, and the abstract
gap then applies verbatim.

The two mathlib imports are the ones that make `B(H_ω)` an ordered C*-algebra:
`CStarAlgebra.ContinuousLinearMap` for the algebra structure and
`InnerProductSpace.StarOrder` for the Loewner order's `StarOrderedRing` and
`NonnegSpectrumClass ℝ`, which are the four instances the abstract gap asks of
its ambient.  Neither was in the development's import graph before, which is
part of why this application had not been made.

## What this does and does not close

It closes the second clause of `NK.05` on the printed objects.  It does not by
itself close `NK.06` or `NK.07`: those need the spectral projection `P` at the
isolated point `1`, the identification of its range with `Fix π(K̄)`,
nonvanishing of `q = 1 − P`, and the lift of `q` to coordinate projections.
`P` exists in `B(H_ω)` by continuous functional calculus at the isolated
spectral point, which is exactly what the gap proved here makes available; the
identification of its range is the next step and is not here.
-/

namespace GroupApproximation
namespace VectorOmegaKazhdanGap

open Filter Matrix
open MarkedCompressionVectorChain VectorHilbertUltraproduct VectorOmegaAction

noncomputable section

universe u

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]
variable {G : Type u} [Group G]

/-- **`π(g) = [V_{g,n}]_ω`, as a unitary of `B(H_ω)`.**

`Analysis/VectorOmegaAction.lean` produces the representation as a homomorphism
into the surjective linear isometries of `H_ω`; `Unitary.linearIsometryEquiv`
is mathlib's identification of those with the unitary group of the bounded
operators, and the gap theorem is stated for the latter. -/
def unitaryOfIsometryRep (π : G →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω)) :
    G →* unitary (VecOmega Y ω →L[ℂ] VecOmega Y ω) :=
  (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := VecOmega Y ω)).symm.toMonoidHom.comp π

/-- The strictly multiplicative case. -/
def repUnitary (V : G →* ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    G →* unitary (VecOmega Y ω →L[ℂ] VecOmega Y ω) :=
  unitaryOfIsometryRep Y ω (rep Y ω V)

/-- **The manuscript's case**: the coordinate family is only `ω`-multiplicative,
which is what an operator-norm asymptotic representation supplies. -/
def repUnitary' (R : OmegaUnitaryRep Y ω G) :
    G →* unitary (VecOmega Y ω →L[ℂ] VecOmega Y ω) :=
  unitaryOfIsometryRep Y ω R.rep'

omit [∀ n, Nonempty (Y n)] in
@[simp] theorem coe_unitaryOfIsometryRep_apply
    (π : G →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω)) (g : G) (x : VecOmega Y ω) :
    ((unitaryOfIsometryRep Y ω π g : VecOmega Y ω →L[ℂ] VecOmega Y ω) : _ → _) x
      = π g x := rfl

/-! ### `H_ω` is nontrivial

Needed only to know `‖h‖ ≤ 1`, which is what supplies the printed lower bound
`−1` of the spectral interval.  A coordinate basis vector at every stage has
mass `1` at every stage, so its class has norm `1`. -/

section Nontrivial

/-- A coordinate basis vector at every stage. -/
def unitFam : VecFam Y := fun n ↦ Pi.single (Classical.arbitrary (Y n)) 1

theorem vecMass_unitFam (n : ℕ) : vecMass (unitFam Y n) = 1 := by
  classical
  have h : ∀ i : (Y n), Complex.normSq (unitFam Y n i)
      = if i = Classical.arbitrary (Y n) then (1 : ℝ) else 0 := by
    intro i
    by_cases hi : i = Classical.arbitrary (Y n)
    · subst hi
      simp [unitFam]
    · simp [unitFam, hi]
  show ∑ i : (Y n), Complex.normSq (unitFam Y n i) = 1
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_ite_eq' Finset.univ]
  simp

theorem unitFam_mem : unitFam Y ∈ vecBounded Y :=
  ⟨1, fun n ↦ le_of_eq (vecMass_unitFam Y n)⟩

/-- `H_ω` has a vector of norm one, so it is nontrivial. -/
instance vecOmega_nontrivial : Nontrivial (VecOmega Y ω) := by
  refine ⟨mkV Y ω ⟨unitFam Y, unitFam_mem Y⟩, 0, ?_⟩
  intro h
  have hnorm : ‖mkV Y ω (⟨unitFam Y, unitFam_mem Y⟩ : vecBounded Y)‖ = 1 := by
    rw [norm_mkV]
    have hfun : (fun n ↦ vecMass (((⟨unitFam Y, unitFam_mem Y⟩ : vecBounded Y) :
        VecFam Y) n)) = fun _ ↦ (1 : ℝ) := funext (vecMass_unitFam Y)
    rw [hfun, UltrafilterLimit.ulim_const]
    simp
  rw [h, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm

end Nontrivial

omit [∀ n, Nonempty (Y n)] in
/-- **`NK.05`, second clause, on the printed objects.**

> for `h = card(S)⁻¹ Σ_{a∈S} π(a)` the Kazhdan pair puts `sp(h)` in
> `[−1, θ] ∪ {1}` with `θ = 1 − ε₀²/(4·card S)`.

`h` is the unitary average of `π` over `S` inside `B(H_ω)`, and the conclusion
is the upper half of the printed spectral inclusion: every real spectral value
other than `1` is at most `θ`.  The lower bound `−1` is automatic — `h` is an
average of unitaries, so `‖h‖ ≤ 1` — and is not part of the Kazhdan input. -/
theorem manuscriptKazhdanSpectralGap_hOmega
    (π : G →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω))
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1)
    {μ : ℝ}
    (hμ : (μ : ℂ) ∈ spectrum ℂ
      (AbstractSpectralGap.unitaryAverage (unitaryOfIsometryRep Y ω π) S))
    (hμ1 : μ ≠ 1) :
    μ ≤ 1 - ε ^ 2 / (4 * S.card) :=
  AbstractSpectralGap.unitaryAverage_spectrum_le (unitaryOfIsometryRep Y ω π) hQ S
    hQS hone hsymm hεone hμ hμ1

/-- **`NK.05`, second clause, as the printed inclusion.**

> `sp(h) ⊆ [−1, θ] ∪ {1}` with `θ = 1 − ε₀²/(4·card S)`.

The set-level statement, not merely the estimate on individual spectral values.
The lower endpoint comes from `‖h‖ ≤ 1`, which holds because `h` averages
unitaries; the upper one is the Kazhdan gap.  This is the form the printed
sentence has, and the form the spectral projection at the isolated point `1` is
taken against. -/
theorem manuscriptSpectrumInclusion_hOmega
    (π : G →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω))
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (S : Finset G) (hS : S.Nonempty) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1) :
    spectrum ℝ (AbstractSpectralGap.unitaryAverage (unitaryOfIsometryRep Y ω π) S)
      ⊆ Set.Icc (-1 : ℝ) (1 - ε ^ 2 / (4 * S.card)) ∪ {(1 : ℝ)} := by
  intro μ hμ
  have hnorm :
      ‖AbstractSpectralGap.unitaryAverage (unitaryOfIsometryRep Y ω π) S‖ ≤ 1 :=
    UltraproductKazhdanProjection.norm_unitaryAverage_le_one
      (unitaryOfIsometryRep Y ω π) hS
  have hle : ‖μ‖ ≤ 1 := le_trans (spectrum.norm_le_norm_of_mem hμ) hnorm
  have hlow : (-1 : ℝ) ≤ μ := neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using hle)
  by_cases hμ1 : μ = 1
  · exact Or.inr hμ1
  · refine Or.inl ⟨hlow, ?_⟩
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ
        (AbstractSpectralGap.unitaryAverage (unitaryOfIsometryRep Y ω π) S) := by
      have h := spectrum.algebraMap_mem ℂ hμ
      rwa [show (algebraMap ℝ ℂ) μ = (μ : ℂ) by simp] at h
    exact manuscriptKazhdanSpectralGap_hOmega Y ω π hQ S hQS hone hsymm hεone
      hμℂ hμ1

/-- **`NK.05`, both clauses, at the manuscript's hypothesis.**

The coordinate family is an operator-norm asymptotic representation -- its
multiplication defects vanish along `ω` and need not vanish at any stage -- and
the conclusion is the printed spectral inclusion for the average of the classes
it defines.  This is the row's sentence with nothing strengthened. -/
theorem manuscriptNormalKazhdanSpectralGap
    (R : OmegaUnitaryRep Y ω G)
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (S : Finset G) (hS : S.Nonempty) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1) :
    spectrum ℝ (AbstractSpectralGap.unitaryAverage (repUnitary' Y ω R) S)
      ⊆ Set.Icc (-1 : ℝ) (1 - ε ^ 2 / (4 * S.card)) ∪ {(1 : ℝ)} :=
  manuscriptSpectrumInclusion_hOmega Y ω R.rep' hQ S hS hQS hone hsymm hεone

end

end VectorOmegaKazhdanGap
end GroupApproximation
