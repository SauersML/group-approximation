import NonsoficGroupsExist.Steinberg.FinitelyGenerated
import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Leavitt.LeavittRankEquivalence
import NonsoficGroupsExist.PropertyT.FiniteFieldElementaryPropertyT

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

/-- The concrete binary-Leavitt Steinberg group is finitely generated in
rank at least three. -/
theorem finitelyGenerated {n : ℕ} (hn : 3 ≤ n) :
    Group.FG (BinaryLeavittSteinberg n) :=
  SteinbergGroup.finitelyGenerated n (by omega)

/-- The elementary binary-Leavitt base has property `(T)` in every rank at
least two.  Rank three is the finite-field EJZ theorem, and the explicit
Leavitt module equivalences identify all positive elementary ranks. -/
theorem elementaryBase_hasKazhdanPropertyT {n : ℕ} (hn : 2 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (ElementaryBase n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply (UniversalLeavitt.family).rankSucc_propertyT_of_rankSucc
    m 2 (by omega) (by omega)
  exact finiteFieldElementaryThree_hasKazhdanPropertyT
    (k := ZMod 2) (A := UniversalLeavitt.BinaryLeavittAlgebra)

/-- If the classical Steinberg kernel vanishes, property `(T)` of the
elementary base transports across the canonical isomorphism.  Thus the
property-`(T)` certificate can be reduced to the concrete `K₂`-vanishing
statement rather than assumed independently. -/
theorem hasKazhdanPropertyT_of_projection_injective {n : ℕ} (hn : 2 ≤ n)
    (hinj : Function.Injective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n)) :
    HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg n) := by
  let e : BinaryLeavittSteinberg n ≃* ElementaryBase n :=
    MulEquiv.ofBijective SteinbergGroup.projection
      ⟨hinj, projection_surjective n⟩
  exact HasKazhdanPropertyT.of_mulEquiv e
    (elementaryBase_hasKazhdanPropertyT hn)

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

/-- The same concrete endpoint with both centrality and property `(T)`
discharged from injectivity of the canonical Steinberg projection.  The
remaining injectivity premise is precisely the classical `K₂`-vanishing
certificate for the binary Leavitt algebra. -/
theorem finitelyPresentedKazhdanSoficImageRigid_of_projection_injective
    {n : ℕ} (hn : 3 ≤ n)
    (hinj : Function.Injective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n))
    [IsSimpleGroup (ElementaryBase n)]
    (hall : AllCountableCentralExtensionsAreNonsofic (ElementaryBase n))
    (hfp : Group.IsFinitelyPresented (BinaryLeavittSteinberg n)) :
    FinitelyPresentedKazhdanSoficImageRigid
      (BinaryLeavittSteinberg n) := by
  have hker : (SteinbergGroup.projection :
      BinaryLeavittSteinberg n →* ElementaryBase n).ker ≤
      Subgroup.center (BinaryLeavittSteinberg n) := by
    rw [MonoidHom.ker_eq_bot SteinbergGroup.projection hinj]
    exact bot_le
  exact finitelyPresentedKazhdanSoficImageRigid_of_certificates hn hker
    hall hfp (hasKazhdanPropertyT_of_projection_injective (by omega) hinj)

end BinaryLeavittSteinberg
end NonsoficGroupsExist
