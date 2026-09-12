import GroupApproximation.Higman.OmegaTowerStaticSeamAffineScan

/-!
# The sole orbit alphabet in the static Omega seam

When zero belongs to `B`, the intrinsic labels of the selected base subgroup
are already translates of the zero Omega label.  Thus the affine alphabet in
the static scan is exactly one orbit alphabet, with no extra summand.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The right-translation orbit of the canonical Omega labels under the
selected first-stage subgroup. -/
def slimOmegaOrbitLabelSet (m : ℕ) (B : Set E) :
    Set (CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m)) :=
  {q | ∃ g : Cent3 (rowOut m), g ∈ slimGenSub m B ∧
    ∃ r, r ∈ omegaLabelSet m B ∧
      q = CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g r}

/-- Under the zero-block hypothesis, the generic affine alphabet is exactly
the single concrete Omega orbit alphabet. -/
theorem affineLabelSet_eq_slimOmegaOrbitLabelSet
    {m : ℕ} {B : Set E} (h0 : (0 : E) ∈ B) :
    CentralHNNFreeLabel.affineLabelSet
        (slimLink m) (slimTransversal m) (slimGenSub m B)
          (omegaLabelSet m B) =
      slimOmegaOrbitLabelSet m B := by
  ext q
  constructor
  · rintro (hq | hq)
    · exact labelSet_slimGenSub_le_omegaOrbit h0 hq
    · exact hq
  · intro hq
    exact Or.inr hq

/-- The strongest static-scan boundary with the redundant intrinsic labels
removed: every returning word is supported on orbit labels which are also row
labels. -/
theorem exists_orbit_boundary_cbWord_of_mem_slimJoin_range
    {m : ℕ} {B : Set E} (h0 : (0 : E) ∈ B) {z : SlimPi m}
    (hzJoin : z ∈ slimWBase m B ⊔ omegaRangeSub m B)
    (hzRange : z ∈ (slimPiF3Hom m).range) :
    ∃ v : FreeGroup ↥Conj.K,
      z = slimPiF3Hom m (Conj.cbHom v) ∧
      slimLabelHom m v ∈ Subgroup.closure (FreeGroup.of ''
        (slimOmegaOrbitLabelSet m B ∩ Set.range (slimRowLabel m))) := by
  obtain ⟨v, hzv, hv⟩ :=
    exists_boundary_cbWord_of_mem_slimJoin_range hzJoin hzRange
  refine ⟨v, hzv, ?_⟩
  rwa [affineLabelSet_eq_slimOmegaOrbitLabelSet h0] at hv

end Omega
end Higman
end GroupApproximation
