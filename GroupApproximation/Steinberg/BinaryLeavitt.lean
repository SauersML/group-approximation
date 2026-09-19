import GroupApproximation.Steinberg.FinitelyGenerated
import GroupApproximation.Steinberg.KervaireSteinberg
import GroupApproximation.Steinberg.FiniteTypePropertyT
import GroupApproximation.Steinberg.HigherRankPropertyT
import GroupApproximation.Steinberg.RootKernelRigidity
import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Leavitt.LeavittRankEquivalence
import GroupApproximation.Leavitt.FiniteFieldLeavitt
import GroupApproximation.Leavitt.FinitePresentation
import GroupApproximation.Leavitt.LeavittSimplicity
import GroupApproximation.PropertyT.FiniteFieldElementaryPropertyT

/-!
# Steinberg groups over the universal binary Leavitt algebra

This file fixes the concrete group appearing in the proposed endpoint and
instantiates the algebraic parts already proved internally: countability,
the canonical surjection to the actual elementary Leavitt group, and
perfectness in rank at least three.
-/

namespace GroupApproximation

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

/-- Every nontrivial homomorphism out of the binary-Leavitt Steinberg group
in rank at least five is injective on every root subgroup.  This is proved
solely from the presented Steinberg relations and the internally established
strong two-sided division theorem for the binary Leavitt algebra. -/
theorem map_root_injective_of_ne_one
    {Q : Type*} [Group Q] {n : ℕ} (hn : 5 ≤ n)
    (φ : BinaryLeavittSteinberg n →* Q) (hφ : φ ≠ 1)
    (i j : Fin n) (hij : i ≠ j) :
    Function.Injective (fun a : UniversalLeavitt.BinaryLeavittAlgebra ↦
      φ (SteinbergGroup.x i j hij a)) :=
  SteinbergGroup.map_x_injective_of_ne_one
    (fun _ ha ↦ BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) ha)
    (SteinbergGroup.fin_exists_spare_four hn) φ hφ i j hij

/-- Every nonzero root element normally generates the explicit Steinberg
group in rank at least five. -/
theorem normalClosure_root_eq_top
    {n : ℕ} (hn : 5 ≤ n) (i j : Fin n) (hij : i ≠ j)
    {a : UniversalLeavitt.BinaryLeavittAlgebra} (ha : a ≠ 0) :
    Subgroup.normalClosure
      ({SteinbergGroup.x i j hij a} : Set (BinaryLeavittSteinberg n)) = ⊤ :=
  SteinbergGroup.normalClosure_x_eq_top
    (fun _ hx ↦ BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx)
    (SteinbergGroup.fin_exists_spare_four hn) hij ha

/-- In every proper normal quotient of the explicit Steinberg group, each
root copy of the binary Leavitt algebra remains faithful. -/
theorem quotient_root_injective
    {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (BinaryLeavittSteinberg n)) [N.Normal] (hN : N ≠ ⊤)
    (i j : Fin n) (hij : i ≠ j) :
    Function.Injective (fun a : UniversalLeavitt.BinaryLeavittAlgebra ↦
      (QuotientGroup.mk' N) (SteinbergGroup.x i j hij a)) :=
  SteinbergGroup.quotientMap_x_injective
    (fun _ hx ↦ BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx)
    (SteinbergGroup.fin_exists_spare_four hn) N hN i j hij

/-- Every proper normal quotient of the binary-Leavitt Steinberg group is
infinite. -/
theorem quotient_infinite
    {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (BinaryLeavittSteinberg n)) [N.Normal] (hN : N ≠ ⊤) :
    Infinite (BinaryLeavittSteinberg n ⧸ N) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  exact Infinite.of_injective
    (fun a : UniversalLeavitt.BinaryLeavittAlgebra ↦
      (QuotientGroup.mk' N)
        (SteinbergGroup.x i j (by simp [i, j]) a))
    (quotient_root_injective hn N hN i j (by simp [i, j]))

/-- Every proper normal quotient of the binary-Leavitt Steinberg group in
rank at least five is perfect. -/
theorem quotient_isPerfect
    {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (BinaryLeavittSteinberg n)) [N.Normal] :
    Group.IsPerfect (BinaryLeavittSteinberg n ⧸ N) := by
  letI : Group.IsPerfect (BinaryLeavittSteinberg n) := isPerfect (by omega)
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)

/-- Every proper normal quotient of the binary-Leavitt Steinberg group in
rank at least five retains property `(T)`. -/
theorem quotient_hasKazhdanPropertyT
    {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (BinaryLeavittSteinberg n)) [N.Normal] :
    HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg n ⧸ N) :=
  HasKazhdanPropertyT.of_surjective
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (hasKazhdanPropertyT hn)

/-- **Unconditional proper-quotient rigidity.**  Every proper normal
quotient is simultaneously infinite, perfect, Kazhdan, and faithful on each
Steinberg root copy of the binary Leavitt algebra.  This is the strongest
quotient statement currently obtained without a centrality theorem for the
unstable Steinberg kernel. -/
theorem properQuotient_rigidity
    {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (BinaryLeavittSteinberg n)) [N.Normal] (hN : N ≠ ⊤) :
    Infinite (BinaryLeavittSteinberg n ⧸ N) ∧
      Group.IsPerfect (BinaryLeavittSteinberg n ⧸ N) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittSteinberg n ⧸ N) ∧
      ∀ (i j : Fin n) (hij : i ≠ j),
        Function.Injective
          (fun a : UniversalLeavitt.BinaryLeavittAlgebra ↦
            (QuotientGroup.mk' N) (SteinbergGroup.x i j hij a)) := by
  exact ⟨quotient_infinite hn N hN, quotient_isPerfect hn N,
    quotient_hasKazhdanPropertyT hn N, quotient_root_injective hn N hN⟩

/-- Every homomorphism from the binary-Leavitt Steinberg group to a finite
group is trivial. -/
theorem hom_eq_one_of_finite
    {Q : Type*} [Group Q] [Finite Q] {n : ℕ} (hn : 5 ≤ n)
    (φ : BinaryLeavittSteinberg n →* Q) :
    φ = 1 := by
  by_contra hφ
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hinjective := map_root_injective_of_ne_one hn φ hφ i j (by simp [i, j])
  have : Finite UniversalLeavitt.BinaryLeavittAlgebra :=
    Finite.of_injective _ hinjective
  exact not_finite UniversalLeavitt.BinaryLeavittAlgebra

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
end GroupApproximation
