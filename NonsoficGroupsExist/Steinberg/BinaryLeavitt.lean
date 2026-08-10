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

/-- Every central extension of the concrete binary-Leavitt Steinberg group
splits in rank at least five.  This is unconditional and does not assert
anything about the kernel of the canonical map to the elementary group. -/
theorem everyCentralExtensionSplits
    {E : Type} [Group E] {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension E (BinaryLeavittSteinberg n)) :
    ∃ s : BinaryLeavittSteinberg n →* E,
      P.projection.comp s = MonoidHom.id _ :=
  KervaireSteinberg.every_centralExtension_splits hn P

end BinaryLeavittSteinberg
end NonsoficGroupsExist
