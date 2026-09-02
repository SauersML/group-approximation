import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity
import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric
import GroupApproximation.GGT.HullSCLemma44KernelAssembly

/-!
# Family-form preservation at fixed filling parameters

This file packages the three relative-isoperimetric outputs used by the
family form of Hull Lemma 4.4.  A prefix control gives the selected auxiliary
family, an ordinary control gives the arbitrary original family, and a control
for a labelled sum family gives the joint conclusion.  The source equalities
for the sum family are kept as fields of the fixed-parameter input, so the
quotient construction has no hidden relabeling step.

The result is the local consumer for Osin's Theorem 4.1 and DGO Theorem
7.19(b).  Its hypotheses are strictly below the canonical family-inclusion
statement: all numerical choices and all small-cancellation certificates are
already fixed.

The last section lifts the fixed-parameter output to the quantified statement.
It names the residual relative-isoperimetric input for the original and joint
families and derives both the repaired family statement and, with the
joint-family selection input, the statement as Theorem C currently consumes it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## Original-family transport -/

/-- An ordinary relative-isoperimetric control gives the canonical image of an
original labelled family. -/
theorem canonicalQuotientFamilyPreservation_of_control
    {G : Type u} [Group G] {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (horiginal : original.IsHyperbolicallyEmbedded)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (control : RelativeIsoperimetricControl original q hq)
    (hinj : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G))) :
    Nonempty (CanonicalQuotientFamilyPreservation q original) := by
  refine ⟨{
    rel := original.mapSurjective q hq
    base_map := rfl
    fam_map := fun _ => rfl
    embedded := control.embedded horiginal
    injOn_peripheralUnion := hinj }⟩

/-! ## Joint transport -/

/-- A labelled sum family is transported through a surjective quotient once
its relative-isoperimetric control is available. -/
theorem quotientJointPeripheralPreservation_of_control
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (control : RelativeIsoperimetricControl joint q hq) :
    Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hjointQ : (joint.mapSurjective q hq).IsHyperbolicallyEmbedded :=
    RelativeIsoperimetricControl.embedded hjointEmbedded control
  refine ⟨{
    rel := joint.mapSurjective q hq
    base_inv := ?_
    fam_original := ?_
    fam_selected := ?_
    embedded := hjointQ }⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x⁻¹, hbaseInv x hx, by simp⟩
  · intro lam
    change (joint.fam (Sum.inl lam)).map q = (original.fam lam).map q
    rw [horiginal lam]
  · intro i
    change (joint.fam (Sum.inr i)).map q =
      (selected.cores.peripheral i).map q
    rw [hselected i]

/-! ## Radius-one support -/

/-- Every original peripheral subgroup is contained in the ambient radius-one
ball when its relative alphabet is included in the ambient alphabet. -/
theorem originalPeripheralUnion_subset_cayleyBall_one
    {G : Type u} [Group G] {A : HullGeneratingSet G}
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier) :
    (⋃ lam : Lambda, (original.fam lam : Set G)) ⊆
      cayleyBall A.alphabet 1 := by
  intro x hx
  obtain ⟨lam, hxlam⟩ := Set.mem_iUnion.mp hx
  rw [mem_cayleyBall_iff, wordDist_one_left]
  exact le_trans
    (wordNorm_le_one_of_mem (hA (GGT.RelGenSet.fam_subset_alphabet
      original lam hxlam))) (by norm_num)

/-! ## Complete fixed-parameter family output -/

/-- The selected, original, and joint preservation objects are assembled from
their three relative controls.  The two injectivity premises are the local
radius consequences of the Greendlinger cut and are shared by all outputs.
-/
theorem familyPreservation_of_controls
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (horiginalEmbedded : original.IsHyperbolicallyEmbedded)
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho)
    (selectedControl : PrefixRelativeIsoperimetricControl selected.rel W
      hsc.toIsSmallCancellation q hq)
    (originalControl : RelativeIsoperimetricControl original q hq)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (jointControl : RelativeIsoperimetricControl joint q hq)
    (hinjA : Set.InjOn q (cayleyBall A.alphabet 1))
    (hinjSelected : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (selected.cores.peripheral i : Set G))) :
    Set.InjOn q (cayleyBall A.alphabet 1) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
      Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hselectedPreserved : Nonempty (QuotientPeripheralPreservation q selected) :=
    quotientPeripheralPreservation_of_prefixIsoperimetricControl selected
      hsc.toIsSmallCancellation q hq selectedControl hinjSelected
  have horiginalUnion : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G)) := by
    intro x hx y hy hxy
    exact hinjA (originalPeripheralUnion_subset_cayleyBall_one original hA hx)
      (originalPeripheralUnion_subset_cayleyBall_one original hA hy) hxy
  have horiginalPreserved :
      Nonempty (CanonicalQuotientFamilyPreservation q original) :=
    canonicalQuotientFamilyPreservation_of_control original horiginalEmbedded q hq
      originalControl horiginalUnion
  have hjointPreserved :
      Nonempty (QuotientJointPeripheralPreservation q selected original) :=
    quotientJointPeripheralPreservation_of_control selected original joint
      hbaseInv horiginal hselected q hq hjointEmbedded jointControl
  exact ⟨hinjA, hselectedPreserved, horiginalPreserved, hjointPreserved⟩

/-! ## Certificate-driven family output -/

/-! At fixed parameters, the relative Greendlinger certificate supplies the
ambient ball injections needed by the three control constructions.  The
selected, original, and joint controls then give the complete family-form
output. -/
theorem familyInclusionConclusion_of_relativeControls
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type u} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (horiginalEmbedded : original.IsHyperbolicallyEmbedded)
    (hcert : ∀ (Z : RelativeReducedDiagram selected.rel W (max R 1)),
      Nonempty (RelativeDiagramCertificate selected.rel W eps mu Z))
    (selectedControl : PrefixRelativeIsoperimetricControl selected.rel W
      hsc.toIsSmallCancellation q hq)
    (originalControl : RelativeIsoperimetricControl original q hq)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (jointControl : RelativeIsoperimetricControl joint q hq) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
      Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hinjRelative : Set.InjOn q
      (cayleyBall selected.rel.alphabet (max R 1)) :=
    injOn_relativeBall_of_relativeDiagramCertificates selected.rel
      hsc.toIsSmallCancellation hmu hthreshold q hker hcert
  have hselectedUnion : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (selected.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    have hxi' : x ∈ selected.rel.fam i := by
      rw [selected.fam_eq i]
      exact hxi
    have hyj' : y ∈ selected.rel.fam j := by
      rw [selected.fam_eq j]
      exact hyj
    apply hinjRelative
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_right R 1)
      exact peripheralUnion_subset_cayleyBall_one selected.rel
        (Set.mem_iUnion.mpr ⟨i, hxi'⟩)
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_right R 1)
      exact peripheralUnion_subset_cayleyBall_one selected.rel
        (Set.mem_iUnion.mpr ⟨j, hyj'⟩)
    · exact hxy
  have hinjAOne : Set.InjOn q (cayleyBall A.alphabet 1) := by
    intro x hx y hy hxy
    apply hinjRelative
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_right R 1)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet
        selected.rel.alphabet (by
          intro z hz
          exact Set.mem_union_left _ (selected.base_le hz)) 1 hx
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_right R 1)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet
        selected.rel.alphabet (by
          intro z hz
          exact Set.mem_union_left _ (selected.base_le hz)) 1 hy
    · exact hxy
  have hinjAR : Set.InjOn q (cayleyBall A.alphabet R) := by
    intro x hx y hy hxy
    apply hinjRelative
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet
        selected.rel.alphabet (by
          intro z hz
          exact Set.mem_union_left _ (selected.base_le hz)) R hx
    · apply cayleyBall_subset_of_le_radius selected.rel.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet
        selected.rel.alphabet (by
          intro z hz
          exact Set.mem_union_left _ (selected.base_le hz)) R hy
    · exact hxy
  obtain ⟨_, hselectedPreserved, horiginalPreserved, hjointPreserved⟩ :=
    familyPreservation_of_controls selected original joint hbaseInv
      horiginal hselected q hq hA horiginalEmbedded hsc selectedControl
      originalControl hjointEmbedded jointControl hinjAOne hselectedUnion
  exact ⟨hinjAR, hselectedPreserved, horiginalPreserved, hjointPreserved⟩

/-! ## A direct local model -/

/-- The fixed-parameter family output specializes to the identity quotient
with the supplied source controls and source family equalities. -/
theorem familyPreservation_identityModel
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (horiginalEmbedded : original.IsHyperbolicallyEmbedded)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    Set.InjOn (MonoidHom.id G) (cayleyBall A.alphabet R) ∧
      Nonempty (CanonicalQuotientFamilyPreservation (MonoidHom.id G) original) ∧
      Nonempty (QuotientJointPeripheralPreservation (MonoidHom.id G)
        selected original) := by
  have hid : Function.Bijective (MonoidHom.id G) :=
    ⟨Function.injective_id, Function.surjective_id⟩
  exact ⟨Function.injective_id.injOn,
    canonicalQuotientFamilyPreservation_of_bijective original horiginalEmbedded
      (MonoidHom.id G) hid,
    quotientJointPeripheralPreservation_of_bijective selected original joint
      hbaseInv horiginal hselected hjointEmbedded (MonoidHom.id G) hid⟩

/-- The selected-family component of the identity model is the existing
quotient-preservation constructor, independently of the arbitrary original
family. -/
theorem selectedPreservation_identityModel
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) :
    Nonempty (QuotientPeripheralPreservation (MonoidHom.id G) selected) := by
  exact quotientPeripheralPreservation_of_bijective selected (MonoidHom.id G)
    ⟨Function.injective_id, Function.surjective_id⟩

/-! ## Leaf B: the family statement from named construction inputs

The selected half of Hull Lemma 4.4 is already reduced to three named
construction statements: the relative Greendlinger certificate, the
kernel-geodesic estimate, and the prefix-kernel cone transfer.  Their assembly
in `HullSCLemma44KernelAssembly` returns ball injectivity and preservation of
the selected auxiliary family.

The family form adds two more conclusions, and each is the image of one
relative-isoperimetric control: an ordinary control for the original labelled
family and one for the source joint family.  Those two controls are the only
remaining input, and they are named below.  Nothing here is new geometry: the
two constructors above do the transport, and the radius-one injectivity both
need is read off the selected assembly at radius `max R 1`.

Why the two controls are not consequences of the three named statements: every
landed control producer, `RelativeIsoperimetricBridgeStatement` included, is
indexed by the same family that carries the relator set `W`.  Here `W` is a set
of words over `RelLetter G (AuxiliaryPeripheralIndex k)`, so those producers
apply to the selected family only; for the original and the joint family the
relator data is not even of the right type.  Osin's Lemma 5.1 for those two
families is exactly the residue named next.
-/

/-- **Osin's relative-isoperimetric conclusion for the two auxiliary families
of Hull Lemma 4.4.**

The quotient is Hull's: it kills the normal closure of a small-cancellation
family over the selected relative generating set.  The conclusion is the pair
of controls the family form needs, one for the original labelled family and
one for the source joint family.  No conclusion about the selected family is
asked for here; that half is already reduced. -/
def FamilyInclusionRelativeControlStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
    ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
      (eps rho : ℕ) (mu : ℝ),
      RelWord.IsLemma44Input selected.rel W eps mu rho →
      ∀ {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Surjective q),
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Nonempty (RelativeIsoperimetricControl original q hq) ∧
            Nonempty (RelativeIsoperimetricControl joint q hq)

/-- The repaired family form follows from the canonical selected-family
statement together with the two residual controls.  The requested radius is
enlarged to `max R 1`, so one application supplies both the prescribed ball
and the radius-one ball carrying every original peripheral letter. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls
    (h44 : HullLemma44CanonicalQuotientStatement.{u})
    (hcontrols : FamilyInclusionRelativeControlStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal joint hbaseInv
    hjointOriginal hjointSelected hjointEmbedded R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h44 selected (max R 1)
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hsc hsurj hker
  obtain ⟨hinjMax, hselectedPreserved⟩ := hgood W q hsc hsurj hker
  have hinjR : Set.InjOn q (cayleyBall A.alphabet R) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_left R 1))
  have hinjOne : Set.InjOn q (cayleyBall A.alphabet 1) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_right R 1))
  obtain ⟨⟨originalControl⟩, ⟨jointControl⟩⟩ :=
    hcontrols selected original joint horiginal hjointEmbedded hjointOriginal
      hjointSelected W eps rho mu hsc q hsurj hker
  have horiginalUnion : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G)) := by
    intro x hx y hy hxy
    exact hinjOne
      (originalPeripheralUnion_subset_cayleyBall_one original hA hx)
      (originalPeripheralUnion_subset_cayleyBall_one original hA hy) hxy
  exact ⟨hinjR, hselectedPreserved,
    canonicalQuotientFamilyPreservation_of_control original horiginal q hsurj
      originalControl horiginalUnion,
    quotientJointPeripheralPreservation_of_control selected original joint
      hbaseInv hjointOriginal hjointSelected q hsurj hjointEmbedded
      jointControl⟩

/-- **Leaf B, repaired form, from named inputs only.**  Three of the four are
the construction statements already carrying the selected half; the fourth is
the residual pair of controls. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls
    (hgeom : RelativeGreendlingerStatement.{u, 0})
    (hkernel : KernelGeodesicEstimateStatement.{u, u, 0})
    (htransfer : PrefixKernelConeTransferStatement.{u, u, 0})
    (hcontrols : FamilyInclusionRelativeControlStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w} :=
  hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls
    (hullLemma44CanonicalQuotientStatement_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer
      hgeom hkernel htransfer)
    hcontrols

/-- **Leaf B as currently stated, from named inputs only.**  The extra
hypothesis over the repaired form is the joint-family selection input, and by
`jointAuxiliaryPeripheralEmbedding_of_familyInclusion` it cannot be avoided:
the leaf entails it. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_controls
    (hgeom : RelativeGreendlingerStatement.{u, 0})
    (hkernel : KernelGeodesicEstimateStatement.{u, u, 0})
    (htransfer : PrefixKernelConeTransferStatement.{u, u, 0})
    (hcontrols : FamilyInclusionRelativeControlStatement.{u, w})
    (hsel : JointAuxiliaryPeripheralEmbedding.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} :=
  hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint hsel
    (hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls
      hgeom hkernel htransfer hcontrols)

end HullSC
end GroupApproximation
