import NonsoficGroupsExist.Steinberg.Perfect
import NonsoficGroupsExist.Endpoint.MainResults

/-!
# Steinberg groups over the universal binary Leavitt algebra

This file fixes the concrete group appearing in the proposed endpoint and
instantiates the algebraic parts already proved internally: countability,
the canonical surjection to the actual elementary Leavitt group, and
perfectness in rank at least three.
-/

namespace NonsoficGroupsExist

/-- The explicit group `St_n(L_{𝔽₂}(1,2))`. -/
noncomputable abbrev BinaryLeavittSteinberg (n : ℕ) :=
  SteinbergGroup (Fin n) UniversalLeavitt.BinaryLeavittAlgebra

namespace BinaryLeavittSteinberg

/-- The actual elementary base `EL_n(L_{𝔽₂}(1,2))`. -/
noncomputable abbrev ElementaryBase (n : ℕ) :=
  elementaryGroup (Fin n) UniversalLeavitt.BinaryLeavittAlgebra

/-- The canonical Steinberg-to-elementary projection is surjective. -/
theorem projection_surjective (n : ℕ) :
    Function.Surjective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n) :=
  SteinbergGroup.projection_surjective

/-- The concrete binary-Leavitt Steinberg group is perfect in rank at least
three. -/
theorem isPerfect {n : ℕ} (hn : 3 ≤ n) :
    Group.IsPerfect (BinaryLeavittSteinberg n) :=
  SteinbergGroup.fin_isPerfect hn

/-- A centrality certificate for the canonical kernel produces the exact
`CentralExtension` consumed by the quotient-rigidity theorem. -/
def centralExtension (n : ℕ)
    (hker : (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n).ker ≤
      Subgroup.center (BinaryLeavittSteinberg n)) :
    CentralExtension (BinaryLeavittSteinberg n) (ElementaryBase n) :=
  SteinbergGroup.centralExtension hker

/-- Concrete endpoint with the still-external classical certificates made
explicit.  The group in the conclusion is the actual presented Steinberg
group, not an abstract placeholder.

The remaining hypotheses correspond to: centrality of the Steinberg kernel
(Kervaire--Steinberg), simplicity of the elementary Leavitt base, the
all-central-covers Kun--Thom theorem, finite presentability
(Krstić--McCool), and property `(T)` (Ershov--Jaikin-Zapirain). -/
theorem finitelyPresentedKazhdanSoficImageRigid_of_certificates
    {n : ℕ} (hn : 3 ≤ n)
    (hker : (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n).ker ≤
      Subgroup.center (BinaryLeavittSteinberg n))
    [IsSimpleGroup (ElementaryBase n)]
    (hall : AllCountableCentralExtensionsAreNonsofic (ElementaryBase n))
    (hfp : Group.IsFinitelyPresented (BinaryLeavittSteinberg n))
    (hT : HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg n)) :
    FinitelyPresentedKazhdanSoficImageRigid
      (BinaryLeavittSteinberg n) := by
  letI : Group.IsPerfect (BinaryLeavittSteinberg n) := isPerfect hn
  exact finitelyPresentedKazhdanSoficImageRigid_of_perfectCentralCover
    (centralExtension n hker) hall hfp hT

end BinaryLeavittSteinberg
end NonsoficGroupsExist
