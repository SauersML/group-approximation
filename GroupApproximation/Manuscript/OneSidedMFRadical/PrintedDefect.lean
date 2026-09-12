import GroupApproximation.Sofic.ManuscriptExactWrappers

/-!
# The printed compression--centralizer defect

`non_mf_groups_exist.tex`, Section~1 (`eq:intrinsic-defect`),
Section~2 (`thm:commutant`) and Theorem~`thm:compression-criterion`.

The manuscript writes the one-sided compressors as a **set**,

`Comp_G(L) = {u : u L u⁻¹ ≤ L}`,

and takes the normal closure of the commutators `[u c u⁻¹, ℓ]` over that set.
The development's `compressionCentralizerDefect` conjugates by an element of
`compressionGroup L`, the *subgroup generated* by the same set.  The printed
object is therefore contained in the formalized one
(`printedDefect_le_compressionCentralizerDefect`), so every obstruction
theorem proved for the larger subgroup applies verbatim to the printed one.
The containment is the only bridge needed, and it runs in the favourable
direction: no statement is weakened by using the development's object, and no
printed statement is strengthened by it.

`Comp_G(L)` itself is already in the development, spelled `compressionSet L`.
`thm:commutant` is carried by `FiniteDimensionalCommutant`; this module
supplies only the printed defect subgroup and the fourth clause of
`thm:compression-criterion`, which is about that subgroup rather than about
the commutant.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

/-! ## `eq:intrinsic-defect`: the printed defect -/

section Defect

variable {G : Type*} [Group G]

/-- The printed defect generators: `[u c u⁻¹, ℓ]` with `u ∈ Comp_G(L)`
(the *set* of one-sided compressors), `c ∈ C_G(L)` and `ℓ ∈ L`. -/
def printedDefectSet (L : Subgroup G) : Set G :=
  {x | ∃ u ∈ compressionSet L, ∃ c : G,
    (∀ ℓ ∈ L, Commute c ℓ) ∧ ∃ ℓ ∈ L, x = ⁅u * c * u⁻¹, ℓ⁆}

/-- `𝔇_G(L)` exactly as printed in `eq:intrinsic-defect`. -/
def printedDefect (L : Subgroup G) : Subgroup G :=
  Subgroup.normalClosure (printedDefectSet L)

instance printedDefect_normal (L : Subgroup G) : (printedDefect L).Normal :=
  Subgroup.normalClosure_normal

theorem printedDefect_generator_mem (L : Subgroup G) {u c ℓ : G}
    (hu : ∀ δ ∈ L, u * δ * u⁻¹ ∈ L) (hc : ∀ δ ∈ L, Commute c δ) (hℓ : ℓ ∈ L) :
    ⁅u * c * u⁻¹, ℓ⁆ ∈ printedDefect L :=
  Subgroup.subset_normalClosure ⟨u, hu, c, hc, ℓ, hℓ, rfl⟩

/-- The printed generating set sits inside the development's generating set:
a single compressor is in particular an element of the group they generate. -/
theorem printedDefectSet_subset (L : Subgroup G) :
    printedDefectSet L ⊆ compressionCentralizerDefectSet L := by
  rintro x ⟨u, hu, c, hc, ℓ, hℓ, rfl⟩
  exact ⟨u, Subgroup.subset_closure hu, c, hc, ℓ, hℓ, rfl⟩

/-- **The bridge.**  The printed defect is contained in the development's
intrinsic compression--centralizer defect. -/
theorem printedDefect_le_compressionCentralizerDefect (L : Subgroup G) :
    printedDefect L ≤ compressionCentralizerDefect L :=
  Subgroup.normalClosure_le_normal fun _ hx ↦
    Subgroup.subset_normalClosure (printedDefectSet_subset L hx)

end Defect

/-- **The last clause of `thm:compression-criterion`.**  Every
finite-dimensional linear representation, over every field, kills the whole
printed defect. -/
def PrintedDefectFiniteDimensionalSterility : Prop :=
  ∀ {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : G →* (V ≃ₗ[k] V)) (L : Subgroup G),
    printedDefect L ≤ ρ.ker

theorem manuscriptPrintedDefectFiniteDimensionalSterility :
    PrintedDefectFiniteDimensionalSterility := by
  intro G k V _ _ _ _ _ ρ L
  exact (printedDefect_le_compressionCentralizerDefect L).trans
    (compressionCentralizerDefect_le_ker ρ L)

end OneSidedMFRadical
end Manuscript
end GroupApproximation
