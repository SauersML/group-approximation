import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Meta.AxiomGuard

/-!
# Quotient calculation in the nondiagonal simplicity argument

The manuscript does not merely use that the double commutators belong to the
normal subgroup.  In each branch it first computes their images in the
quotient: the conjugated root has the same image as the original root, so the
double commutator becomes the commutator of two commuting roots and is
therefore trivial.  `commutator_conj_mem` contains this calculation inside its
proof, but its conclusion exposes only subgroup membership.  The declaration
below records the full quotient calculation as stated in the manuscript.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u

/-- The exact quotient-image calculation used in both nondiagonal branches.
All group and normal-subgroup data occur inside the proposition, so this is an
unconditional statement rather than a wrapper around an assumed quotient
identity. -/
def ConjugateCommutatorImageIsTrivial : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (g e f : G), g ∈ N → e * f = f * e →
      let pi : G →* G ⧸ N := QuotientGroup.mk' N
      pi (g * e * g⁻¹) = pi e ∧
        pi ⁅g * e * g⁻¹, f⁆ = ⁅pi e, pi f⁆ ∧
          ⁅pi e, pi f⁆ = 1 ∧
            pi ⁅g * e * g⁻¹, f⁆ = 1

/-- **“In `H/N`, the left-hand side is the commutator of the two original
elementary matrices, hence is trivial.”** -/
theorem manuscriptConjugateCommutatorImageIsTrivial :
    ConjugateCommutatorImageIsTrivial := by
  intro G _ N _ g e f hg hef
  let pi : G →* G ⧸ N := QuotientGroup.mk' N
  have hg1 : pi g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have hconj : pi (g * e * g⁻¹) = pi e := by
    rw [map_mul, map_mul, map_inv, hg1, one_mul, inv_one, mul_one]
  have hmap : pi ⁅g * e * g⁻¹, f⁆ = ⁅pi e, pi f⁆ := by
    calc
      pi ⁅g * e * g⁻¹, f⁆ =
          pi (g * e * g⁻¹) * pi f * (pi (g * e * g⁻¹))⁻¹ * (pi f)⁻¹ := by
            rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
              map_inv]
      _ = pi e * pi f * (pi e)⁻¹ * (pi f)⁻¹ := by rw [hconj]
      _ = ⁅pi e, pi f⁆ := by rw [commutatorElement_def]
  have hcommute : Commute (pi e) (pi f) := by
    show pi e * pi f = pi f * pi e
    rw [← map_mul, ← map_mul, hef]
  have htrivial : ⁅pi e, pi f⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr hcommute
  exact ⟨hconj, hmap, htrivial, hmap.trans htrivial⟩

#audit_closed_axioms manuscriptConjugateCommutatorImageIsTrivial

end OneSidedMFRadical
end Manuscript
end GroupApproximation
