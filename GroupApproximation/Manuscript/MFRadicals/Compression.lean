import GroupApproximation.Sofic.TorsionSpectralCollapse

/-!
# The analytic engine: one-sided Kazhdan compression

The reusable mechanism behind every non-MF construction in the paper.  A
Kazhdan subgroup `L ≤ E` compressed into itself by a one-sided compressor `s`
forces every corona representation to identify a finite-order witness with its
whole `L`-conjugation orbit.  The resulting *torsion-collapse defect* therefore
lies in the MF radical, with no analytic hypothesis left over: the spectral
gate is discharged at every order by the Fourier idempotents of a finite-order
unitary, which is finite linear algebra.

When the defect quotient happens to be MF the same theorem computes the radical
exactly.  Both halves are used later: `PerfectLampExact` is the case where the
quotient is MF because the acting group is, and `FullRadical` is the case where
the defect is everything.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- Quotients of countable groups are countable; mirrored locally, as in the
implementation modules where the same instance is `local`. -/
local instance quotientCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] : Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- **The compression engine.**  For a Kazhdan subgroup with a one-sided
compressor the torsion-collapse defect lies in the MF radical, and equals it as
soon as the defect quotient is MF. -/
def KazhdanCompressionCollapse : Prop :=
  ∀ (E : Type) [Group E] [Countable E] (L : Subgroup E),
    HasKazhdanPropertyT.{0, 0} ↥L → ∀ s : E, (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      TorsionCompressionCollapse.torsionCollapseDefect L s ≤
          actualCoronaMFResidual E ∧
        (IsCDEOperatorMF
            (E ⧸ TorsionCompressionCollapse.torsionCollapseDefect L s) →
          actualCoronaMFResidual E =
            TorsionCompressionCollapse.torsionCollapseDefect L s)

theorem manuscriptCompressionCollapse : KazhdanCompressionCollapse := by
  intro E _ _ L hT s hcomp
  exact ⟨TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan
      hT hcomp,
    fun hq =>
      TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan
        hT hcomp hq⟩

end MFRadicals
end Manuscript
end GroupApproximation
