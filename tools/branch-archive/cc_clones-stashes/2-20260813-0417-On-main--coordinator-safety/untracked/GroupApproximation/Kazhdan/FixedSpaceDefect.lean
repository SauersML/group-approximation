import GroupApproximation.Kazhdan.FixedSpaceStabilizer
import GroupApproximation.Kazhdan.KazhdanOrthogonal

/-!
# Fixed-sector annihilation of the intrinsic compression defect

This file isolates the representation-theoretic back half of the intrinsic
compression--centralizer argument.  Suppose a homomorphism `φ : H → K` is
realized by vectors in an orthogonal representation of `H`, with conjugation
in `K` corresponding to the orthogonal action.  If every one-sided compressor
stabilizes the `L`-fixed sector, then `φ` kills the entire intrinsic
compression--centralizer defect `𝔇(H,L)`.

The analytic front half of the application proves the stabilization hypothesis
using the Kazhdan projection and stable finiteness.  The theorem below then
handles all products, inverse compressors, defect generators, and their normal
closure at once.
-/

namespace GroupApproximation
namespace FixedSpaceDefect

open scoped commutatorElement

variable {H K E : Type} [Group H] [Group K]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If conjugation is represented faithfully by vectors and every one-sided
compressor stabilizes the `L`-fixed sector, then every intrinsic
compression--centralizer defect lies in the kernel. -/
theorem compressionCentralizerDefect_le_ker
    (ρ : H →* (E ≃ₗᵢ[ℝ] E)) (φ : H →* K) (v : K → E)
    (hv : Function.Injective v)
    (hequiv : ∀ g h : H,
      ρ g (v (φ h)) = v (φ (g * h * g⁻¹)))
    (L : Subgroup H)
    (hcompression : compressionSet L ⊆
      FixedSpaceStabilizer.stabilizer ρ
        (KazhdanOrthogonal.invariantSubmodule (ρ.comp L.subtype))) :
    compressionCentralizerDefect L ≤ φ.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, hg, z, hz, ell, hell, rfl⟩
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  let S : Submodule ℝ E :=
    KazhdanOrthogonal.invariantSubmodule (ρ.comp L.subtype)
  have hzfixed : v (φ z) ∈ S := by
    change v (φ z) ∈
      KazhdanOrthogonal.invariantSubmodule (ρ.comp L.subtype)
    rw [KazhdanOrthogonal.mem_invariantSubmodule]
    intro delta
    have hconj : (delta : H) * z * (delta : H)⁻¹ = z := by
      rw [← (hz delta delta.property).eq]
      simp
    calc
      (ρ.comp L.subtype) delta (v (φ z))
          = v (φ ((delta : H) * z * (delta : H)⁻¹)) :=
            hequiv (delta : H) z
      _ = v (φ z) := by rw [hconj]
  have hgzfixed : ρ g (v (φ z)) ∈ S :=
    FixedSpaceStabilizer.compressionGroup_map_mem
      ρ L S hcompression hg hzfixed
  have hafixed : v (φ (g * z * g⁻¹)) ∈ S := by
    rw [← hequiv g z]
    exact hgzfixed
  have hellfixed :=
    (KazhdanOrthogonal.mem_invariantSubmodule (ρ.comp L.subtype)
      (v (φ (g * z * g⁻¹)))).mp hafixed ⟨ell, hell⟩
  have hconjmap :
      φ (ell * (g * z * g⁻¹) * ell⁻¹) = φ (g * z * g⁻¹) := by
    apply hv
    calc
      v (φ (ell * (g * z * g⁻¹) * ell⁻¹))
          = ρ ell (v (φ (g * z * g⁻¹))) :=
            (hequiv ell (g * z * g⁻¹)).symm
      _ = v (φ (g * z * g⁻¹)) := by
        simpa using hellfixed
  have hconjmap' :
      φ ell * φ (g * z * g⁻¹) * (φ ell)⁻¹ = φ (g * z * g⁻¹) := by
    simpa only [map_mul, map_inv] using hconjmap
  apply Commute.symm
  show φ ell * φ (g * z * g⁻¹) = φ (g * z * g⁻¹) * φ ell
  calc
    φ ell * φ (g * z * g⁻¹)
        = (φ ell * φ (g * z * g⁻¹) * (φ ell)⁻¹) * φ ell := by group
    _ = φ (g * z * g⁻¹) * φ ell := by rw [hconjmap']

end FixedSpaceDefect
end GroupApproximation
