import GroupApproximation.Higman.AmalgamTorsion
import GroupApproximation.Algebra.PushoutITorsionFree

/-!
# Torsion in an amalgam, in conjugate-into-a-factor form

`Algebra.PushoutITorsionFree.exists_conj_into_factor` returns two cases for an
element of finite order: it is in the base, or it is conjugate into a factor.
For most purposes that is one case, because the base embeds in every factor,
and this file records the merged form --- `exists_conj_into_factor_of_pow`.

Nothing technical keeps it out of `Higman.AmalgamTorsion` --- that file now
imports the `Algebra` module too --- so folding it back in is a free move
whenever the root import of this module is dropped in the same change.

## History

Until 2026-08-22 this file also carried two theorems arguing that
`Higman.AmalgamTorsion`'s gated input was never load-bearing.  That gate has
since been deleted and its consumer restated unconditionally, so both went with
it: one named a statement that no longer exists, and the other is now
`AmalgamTorsion.isPowerTorsionFree_pushoutI` itself.  What is below is the part
that was never about the gate. -/

namespace GroupApproximation
namespace Higman
namespace AmalgamTorsion

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **An element of finite order in an amalgam is conjugate into a factor.**

`PushoutITorsionFree.exists_conj_into_factor` returns the base case separately;
it is the factor case as well, because the base embeds in every factor and `ι`
is nonempty. -/
theorem exists_conj_into_factor_of_pow [Nonempty ι]
    (hφ : ∀ i, Function.Injective (φ i)) {x : PushoutI φ} {n : ℕ} (hn : 0 < n)
    (hxn : x ^ n = 1) :
    ∃ (c : PushoutI φ) (i : ι) (g : G i), x = c * of (φ := φ) i g * c⁻¹ := by
  have i₀ : ι := Classical.arbitrary ι
  rcases PushoutITorsionFree.exists_conj_into_factor hφ hn hxn with
    ⟨h, rfl⟩ | ⟨c, j, m, hc⟩
  · refine ⟨1, i₀, φ i₀ h, ?_⟩
    rw [of_apply_eq_base φ i₀]
    group
  · refine ⟨c⁻¹, j, m, ?_⟩
    rw [← hc]
    group

end AmalgamTorsion
end Higman
end GroupApproximation
