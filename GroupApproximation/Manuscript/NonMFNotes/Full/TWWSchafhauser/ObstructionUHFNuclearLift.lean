import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffros
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionUHFModelLift

/-!
# Nuclear `⋆`-homomorphisms into `Q_ω` and locally quasidiagonal traces

Lane `TWWSchafhauser-3d1` (work order `WO-TWWSchafhauser-3d-1`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), 291--304, §5.

The last step of Schafhauser's argument takes a unital `⋆`-homomorphism
`ψ : A → Q_ω` out of a separable nuclear C⋆-algebra `A` and produces ucp maps
`A → Q` along `ω`.  The ucp lift exists by the Choi--Effros lifting theorem
(`exists_ucp_lift_of_isNuclear`, `ChoiEffros.lean`), because the quotient map
`ℓ^∞(ℕ, Q) → Q_ω` is a surjective `⋆`-homomorphism.  This file packages that lift
as a `ProductCoronaLift` and joins it to `isLocallyQuasidiagonalTrace_of_productCoronaLift`.

## Main declarations

* `exists_productCoronaLift_of_isNuclear`: a unital `⋆`-homomorphism from a separable
  nuclear C⋆-algebra into a constant-coefficient product corona has a ucp lift.
* `hasUHFFilterModel_of_isNuclear_of_coronaHom`,
  `isLocallyQuasidiagonalTrace_of_isNuclear_of_coronaHom`: if every `ψ a` has a
  representative whose `Q`-traces converge to `τ a` along `ω`, then `τ` is a locally
  quasidiagonal trace.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter GroupApproximation.PolarLiftingGeneralCStar GroupApproximation.Quasidiagonal

noncomputable section

universe u v

/-- **Choi--Effros lift into a product corona** (Schafhauser, Crelle 759 (2020), §5).
A unital `⋆`-homomorphism `ψ : A → B_l` out of a separable nuclear C⋆-algebra has a
ucp lift `A → ℓ^∞(ℕ, B)`, i.e. it is the `hom` of a `ProductCoronaLift`. -/
theorem exists_productCoronaLift_of_isNuclear {A : Type v} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] [Nontrivial A] {B : Type u} [CStarAlgebra B]
    [Nontrivial B] {l : Filter ℕ} (hA : CStarExactness.IsNuclearCStarAlgebra A)
    (ψ : A →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ B) l) :
    ∃ L : ProductCoronaLift A B l, L.hom = ψ := by
  obtain ⟨L, hL, hL1, hLπ⟩ := exists_ucp_lift_of_isNuclear hA
    (cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l)
    (cStarProductCoronaQuotient_surjective (fun _ : ℕ ↦ B) l)
    (ψ : A →ₗ[ℂ] CStarProductCorona (fun _ : ℕ ↦ B) l)
    (CStarExactness.isCompletelyPositive_of_starAlgHom ψ.toNonUnitalStarAlgHom)
    (map_one ψ)
  exact ⟨⟨ψ, L, hL1, hL, hLπ⟩, rfl⟩

section Endpoint

variable {Q : Type} [CStarAlgebra Q] [Nontrivial Q] {A : Type u} [CStarAlgebra A]
  [TopologicalSpace.SeparableSpace A] [Nontrivial A]

/-- **A nuclear `⋆`-homomorphism into `Q_ω` inducing `τ` gives a UHF filter model**
(Schafhauser, Crelle 759 (2020), §5).  Every `ψ a` needs a representative whose
`Q`-traces converge to `τ a` along `ω`. -/
theorem hasUHFFilterModel_of_isNuclear_of_coronaHom (M : UHFModel Q)
    (hA : CStarExactness.IsNuclearCStarAlgebra A) (τ : A → ℂ) (ω : Ultrafilter ℕ)
    (ψ : A →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ Q) (ω : Filter ℕ))
    (htr : ∀ a : A, ∃ x : BoundedCStarSequence (fun _ : ℕ ↦ Q),
      cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) (ω : Filter ℕ) x = ψ a ∧
        Tendsto (fun n ↦ ‖τ a - M.trace (x n)‖) (ω : Filter ℕ) (nhds 0)) :
    HasUHFFilterModel M τ := by
  obtain ⟨L, rfl⟩ := exists_productCoronaLift_of_isNuclear hA ψ
  choose seq hseq htr' using htr
  exact hasUHFFilterModel_of_productCoronaLift M τ ω L seq hseq htr'

/-- **A nuclear `⋆`-homomorphism into `Q_ω` inducing `τ` makes `τ` locally
quasidiagonal** (Schafhauser, Crelle 759 (2020), §§4--5, the last step). -/
theorem isLocallyQuasidiagonalTrace_of_isNuclear_of_coronaHom (M : UHFModel Q)
    (hA : CStarExactness.IsNuclearCStarAlgebra A) (τ : A → ℂ) (ω : Ultrafilter ℕ)
    (ψ : A →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ Q) (ω : Filter ℕ))
    (htr : ∀ a : A, ∃ x : BoundedCStarSequence (fun _ : ℕ ↦ Q),
      cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) (ω : Filter ℕ) x = ψ a ∧
        Tendsto (fun n ↦ ‖τ a - M.trace (x n)‖) (ω : Filter ℕ) (nhds 0)) :
    IsLocallyQuasidiagonalTrace τ :=
  isLocallyQuasidiagonalTrace_of_hasUHFFilterModel
    (hasUHFFilterModel_of_isNuclear_of_coronaHom M hA τ ω ψ htr)

end Endpoint

end

end GroupApproximation.Full.TWWSchafhauser
