import GroupApproximation.Criterion.CompressionCentralizerDefect

/-!
# Finite-dimensional commutant rigidity for the one-sided Kazhdan manuscript

This is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Theorem `thm:commutant`.

The commutant of `ρ(L)` is represented as the fixed submodule of the
adjoint representation on `End_k(V)`. Consequently, its image under
`Ad(ρ(u))` is exactly the displayed conjugate
`ρ(u) ρ(L)' ρ(u)⁻¹` from the manuscript.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u v w

/-- **Theorem `thm:commutant`.** A one-sided compressor acts surjectively on
the commutant in every finite-dimensional linear representation. Every
commutator formed from a conjugated centralizer element is therefore killed.
-/
def FiniteDimensionalCommutantRigidity : Prop :=
  ∀ (G : Type u) (k : Type v) (V : Type w)
    [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : G →* (V ≃ₗ[k] V))
    (L : Subgroup G) (compressor : G),
    (∀ ell ∈ L, compressor * ell * compressor⁻¹ ∈ L) →
      (fixedSubmodule (adjointRep rho) L).map
          (adjointRep rho compressor : Module.End k (Module.End k V)) =
        fixedSubmodule (adjointRep rho) L ∧
      ∀ centralizer : G, (∀ ell ∈ L, Commute centralizer ell) →
        ∀ ell ∈ L,
          rho ⁅compressor * centralizer * compressor⁻¹, ell⁆ = 1

/-- Closed proof of the manuscript's finite-dimensional commutant theorem. -/
theorem manuscriptFiniteDimensionalCommutantRigidity :
    FiniteDimensionalCommutantRigidity := by
  intro G k V _ _ _ _ _ rho L compressor hcompressor
  refine ⟨fixedSubmodule_map_eq (adjointRep rho) L hcompressor, ?_⟩
  intro centralizer hcentralizer ell hell
  have hset : compressor ∈ compressionSet L := hcompressor
  have hgroup : compressor ∈ compressionGroup L :=
    Subgroup.subset_closure hset
  exact map_compressionCentralizerDefect_generator_eq_one
    rho L hgroup hcentralizer hell

end OneSidedMFRadical
end Manuscript
end GroupApproximation
