import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed endpoints for four statements of `sec:compression-radical`

`non_mf_groups_exist.tex`, tex line numbers at 68481e4d7.

Four declarations carry printed sentences of this section, but their types begin with binders,
so `#audit_closed_axioms` rejects them as stated. On main they carry only `#audit_axioms`.
This module states each sentence as a named `Prop` and proves it with the existing declaration,
so every endpoint gets a closed audit. Nothing is re-proved, and no existing file changes.

* tex 364–366, `prop:mf-residual-calculus`: "Every homomorphism from `G` to an MF group is trivial
  on `K` if and only if every corona homomorphism from `G` is trivial on `K`."
  (`OneSidedMFRadical.allMFTargetsKill_iff_allCoronasKill`)
* tex 366–368: "Let `A` be a unital `C^*`-algebra and let `π : G → U(A)` be an injective group
  homomorphism. If `A` embeds in a norm matrix corona, then `G` is MF."
  (`isCDEOperatorMF_of_faithful_corona_map`)
* tex 395–400: the exact commutant count for an actual representation, and `ρ` trivial on
  `𝔇_G(L)`. (`CompressionCriterionSentences.manuscriptSentence_exactRepresentationCommutantDimensionCount`)
* tex 402–403: "Property (T) supplies a Kazhdan projection in its place, and stable finiteness of
  the corona replaces the dimension count."
  (`CompressionCriterionSentences.manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount`)
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open scoped commutatorElement

universe u v w

/-- **tex 364–366 (`prop:mf-residual-calculus`, first assertion).** For countable `G` and
`K ≤ G`, every homomorphism to an MF group kills `K` if and only if every corona homomorphism
kills `K`. -/
def PrintedAllMFTargetsKillIffAllCoronasKill : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G),
    (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
      ∀ f : G →* M, K ≤ f.ker) ↔
    (∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
      (∀ n, 0 < Fintype.card (X n)) →
      ∀ Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        K ≤ Theta.ker)

theorem printedAllMFTargetsKillIffAllCoronasKill :
    PrintedAllMFTargetsKillIffAllCoronasKill := by
  intro G _ _ K
  exact OneSidedMFRadical.allMFTargetsKill_iff_allCoronasKill G K

/-- **tex 366–368 (`prop:mf-residual-calculus`, second assertion).** A countable group with an
injective homomorphism into the unitary group of a `C^*`-algebra that embeds, possibly
nonunitally, in a norm matrix corona is MF. -/
def PrintedFaithfulCoronaMapGivesMF : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] (A : Type v) [CStarAlgebra A]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    (∀ n, 0 < Fintype.card (X n)) →
    ∀ e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n), Function.Injective e →
    ∀ rho : G →* unitary A, Function.Injective rho → IsCDEOperatorMF G

theorem printedFaithfulCoronaMapGivesMF : PrintedFaithfulCoronaMapGivesMF.{u, v} := by
  intro G _ _ A _ X _ hX e he rho hrho
  exact isCDEOperatorMF_of_faithful_corona_map X hX e he rho hrho

/-- **tex 395–400.** For an actual finite-dimensional representation `ρ` and `u` with
`uLu⁻¹ ≤ L`, conjugation by `ρ(u)` maps the commutant of `ρ(L)` onto itself, `ρ(ucu⁻¹)`
commutes with `ρ(L)` for every `c` commuting with `L`, and `ρ` is trivial on `𝔇_G(L)`. -/
def PrintedExactRepresentationCommutantDimensionCount : Prop :=
  ∀ (G : Type u) (k : Type v) (V : Type w) [Group G] [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G),
    (∀ ell ∈ L, u * ell * u⁻¹ ∈ L) →
    (fixedSubmodule (adjointRep rho) L).map
        (adjointRep rho u : Module.End k (Module.End k V)) =
      fixedSubmodule (adjointRep rho) L ∧
      (∀ c : G, (∀ ell ∈ L, Commute c ell) → ∀ ell ∈ L,
        rho ⁅u * c * u⁻¹, ell⁆ = 1) ∧
      OneSidedMFRadical.printedDefect L ≤ rho.ker

theorem printedExactRepresentationCommutantDimensionCount :
    PrintedExactRepresentationCommutantDimensionCount.{u, v, w} := by
  intro G k V _ _ _ _ _ rho L u hu
  exact OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_exactRepresentationCommutantDimensionCount
    rho L u hu

/-- **tex 402–403.** For a group with property (T): a Kazhdan datum exists, whose spectral
projection is the Kazhdan projection, and the norm matrix corona is stably finite. -/
def PrintedKazhdanProjectionAndStableFinitenessReplaceTheCount : Prop :=
  ∀ (L : Type) [Group L], HasKazhdanPropertyT.{0, 0} L →
    Nonempty (MaximalCStarKazhdanProjection.KazhdanData L) ∧
      OneSidedMFRadical.NormMatrixCoronaStableFinite

theorem printedKazhdanProjectionAndStableFinitenessReplaceTheCount :
    PrintedKazhdanProjectionAndStableFinitenessReplaceTheCount := by
  intro L _ hL
  exact OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount
    L hL

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.printedAllMFTargetsKillIffAllCoronasKill
#audit_closed_axioms
  Manuscript.NonMFSentences.printedFaithfulCoronaMapGivesMF
#audit_closed_axioms
  Manuscript.NonMFSentences.printedExactRepresentationCommutantDimensionCount
#audit_closed_axioms
  Manuscript.NonMFSentences.printedKazhdanProjectionAndStableFinitenessReplaceTheCount
