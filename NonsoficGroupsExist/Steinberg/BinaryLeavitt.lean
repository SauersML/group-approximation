import NonsoficGroupsExist.Steinberg.FinitelyGenerated
import NonsoficGroupsExist.Steinberg.KervaireSteinberg
import NonsoficGroupsExist.Steinberg.FiniteTypePropertyT
import NonsoficGroupsExist.Steinberg.HigherRankPropertyT
import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Leavitt.LeavittRankEquivalence
import NonsoficGroupsExist.Leavitt.FiniteFieldLeavitt
import NonsoficGroupsExist.Leavitt.FinitePresentation
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

/-- The binary-Leavitt Steinberg group in rank three has property `(T)`
directly, without assuming that the unstable Steinberg kernel vanishes. -/
theorem rankThree_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg 3) :=
  finiteTypeSteinbergThree_hasKazhdanPropertyT

/-- The binary-Leavitt Steinberg group has property `(T)` in every rank at
least five.  The proof uses the explicit complete left-comb matrix family
inside the coefficient ring and the unconditional higher-rank block-root
theorem; it does not use the canonical projection to the elementary group. -/
theorem hasKazhdanPropertyT {n : ℕ} (hn : 5 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  letI : CharP UniversalLeavitt.BinaryLeavittAlgebra 2 :=
    charP_of_injective_algebraMap (R := ZMod 2)
      (RingHom.injective
        (algebraMap (ZMod 2) UniversalLeavitt.BinaryLeavittAlgebra)) 2
  let F : CompleteMatrixFamily UniversalLeavitt.BinaryLeavittAlgebra
      (Fin (m + 1)) :=
    UniversalLeavitt.family.prefixMatrixFamily (leftCombCode m)
      (UniversalLeavitt.family.leftCombCode_complete m)
  have hblock : HasKazhdanPropertyT
      (SteinbergGroup (Fin 2 ⊕ Fin (m + 1))
        UniversalLeavitt.BinaryLeavittAlgebra) :=
    finiteTypeBlockSteinberg_hasKazhdanPropertyT F (by simp)
  let e : (Fin 2 ⊕ Fin (m + 1)) ≃ Fin (m + 3) :=
    finSumFinEquiv.trans (finCongr (by omega))
  exact HasKazhdanPropertyT.of_mulEquiv
    (SteinbergGroup.reindexEquiv e).symm hblock

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

/-- Every elementary binary-Leavitt rank at least two is nonsofic.  The
rank-four compression theorem supplies the obstruction, and the explicit
Leavitt rank equivalences transport it to arbitrary rank. -/
theorem elementaryBase_not_isSofic {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSofic (ElementaryBase n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let e : ElementaryBase (m + 1) ≃*
      FiniteFieldLeavitt.Ambient (ZMod 2) :=
    (UniversalLeavitt.family).rankSuccEquiv m 3 (by omega) (by omega)
  intro hsofic
  exact FiniteFieldLeavitt.ambient_not_isSofic (ZMod 2)
    (isSofic_of_injective e.symm.toMonoidHom e.symm.injective hsofic)

/-- The canonical Steinberg projection as an isomorphism, conditional on
vanishing of the **unstable** Steinberg kernel `K₂(n,L)`.  No such
vanishing or stability theorem is proved here. -/
noncomputable def projectionEquiv (n : ℕ)
    (hinj : Function.Injective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n)) :
    BinaryLeavittSteinberg n ≃* ElementaryBase n :=
  MulEquiv.ofBijective SteinbergGroup.projection
    ⟨hinj, projection_surjective n⟩

/-- Vanishing of the Steinberg kernel also transports the established
nonsoficity of the elementary base to the Steinberg group. -/
theorem not_isSofic_of_projection_injective {n : ℕ} (hn : 2 ≤ n)
    (hinj : Function.Injective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n)) :
    ¬ IsSofic (BinaryLeavittSteinberg n) := by
  intro hsofic
  exact elementaryBase_not_isSofic hn
    (isSofic_of_injective (projectionEquiv n hinj).symm.toMonoidHom
      (projectionEquiv n hinj).symm.injective hsofic)

/-- A centrality certificate for the canonical kernel produces the exact
`CentralExtension` consumed by the quotient-rigidity theorem. -/
def centralExtension (n : ℕ)
    (hker : (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n).ker ≤
      Subgroup.center (BinaryLeavittSteinberg n)) :
    CentralExtension (BinaryLeavittSteinberg n) (ElementaryBase n) :=
  SteinbergGroup.centralExtension hker

/-- Every central extension of the concrete binary-Leavitt Steinberg group
splits in rank at least five.  This is unconditional and does not assert
anything about the kernel of the canonical map to the elementary group. -/
theorem everyCentralExtensionSplits
    {E : Type} [Group E] {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension E (BinaryLeavittSteinberg n)) :
    ∃ s : BinaryLeavittSteinberg n →* E,
      P.projection.comp s = MonoidHom.id _ :=
  KervaireSteinberg.every_centralExtension_splits hn P

/-- Conditional only on centrality of the canonical Steinberg kernel, the
binary-Leavitt Steinberg projection is the universal central extension in
rank at least five.  In particular, this theorem neither assumes nor proves
injectivity of the projection. -/
noncomputable def universalCentralExtension_of_kernel_central
    {n : ℕ} (hn : 5 ≤ n)
    (hker : (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n).ker ≤
      Subgroup.center (BinaryLeavittSteinberg n)) :
    UniversalCentralExtension (BinaryLeavittSteinberg n)
      (ElementaryBase n) :=
  KervaireSteinberg.fin_universalCentralExtension hn hker

/-- A shorter endpoint conditional on **unstable** `K₂(n,L)=0`.
Injectivity identifies the Steinberg group with its simple elementary base.
Its nonsoficity therefore rules out every nontrivial quotient directly, with
no all-central-covers stability premise.  The injectivity hypothesis remains
an external certificate. -/
theorem finitelyPresentedKazhdanSoficImageRigid_of_projection_injective
    {n : ℕ} (hn : 5 ≤ n)
    (hinj : Function.Injective
      (SteinbergGroup.projection :
        BinaryLeavittSteinberg n →* ElementaryBase n))
    [IsSimpleGroup (ElementaryBase n)]
    (hfp : Group.IsFinitelyPresented (BinaryLeavittSteinberg n)) :
    FinitelyPresentedKazhdanSoficImageRigid
      (BinaryLeavittSteinberg n) := by
  letI : IsSimpleGroup (BinaryLeavittSteinberg n) :=
    (projectionEquiv n hinj).isSimpleGroup
  exact finitelyPresentedKazhdanSoficImageRigid_of_quotientObstruction
    hfp (hasKazhdanPropertyT hn)
    (everyNontrivialQuotientIsNonsofic_of_isSimpleGroup
      (not_isSofic_of_projection_injective (by omega) hinj))

end BinaryLeavittSteinberg
end NonsoficGroupsExist
