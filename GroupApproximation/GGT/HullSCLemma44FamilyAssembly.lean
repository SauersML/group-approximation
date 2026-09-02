import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity
import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric
import GroupApproximation.GGT.HullSCLemma44KernelAssembly
import GroupApproximation.GGT.HullSCLemma44Canonical

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
      (⋃ lam : Lambda, (original.fam lam : Set G))) (Y : Set G) :
    Nonempty (CanonicalQuotientFamilyPreservation q original Y) := by
  refine ⟨{
    rel := original.mapSurjective q hq
    base_map := ⟨∅, Set.finite_empty, Set.empty_subset Y, by
      intro y hy
      rw [Set.union_empty]
      exact hy⟩
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
    (hjointSub : ∃ T : Set G, T.Finite ∧ joint.base ⊆ original.base ∪ T)
    (control : RelativeIsoperimetricControl joint q hq) :
    Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hjointQ : (joint.mapSurjective q hq).IsHyperbolicallyEmbedded :=
    RelativeIsoperimetricControl.embedded hjointEmbedded control
  refine ⟨{
    rel := joint.mapSurjective q hq
    base_inv := ?_
    fam_original := ?_
    fam_selected := ?_
    embedded := hjointQ
    base_subset := by
      obtain ⟨T, hT, hsub⟩ := hjointSub
      exact ⟨T, hT, Set.image_mono hsub⟩ }⟩
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
    (hjointSub : ∃ T : Set G, T.Finite ∧ joint.base ⊆ original.base ∪ T)
    (jointControl : RelativeIsoperimetricControl joint q hq)
    (hinjA : Set.InjOn q (cayleyBall A.alphabet 1))
    (hinjSelected : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (selected.cores.peripheral i : Set G))) :
    Set.InjOn q (cayleyBall A.alphabet 1) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q original
        selected.rel.alphabet.carrier) ∧
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
      Nonempty (CanonicalQuotientFamilyPreservation q original
        selected.rel.alphabet.carrier) :=
    canonicalQuotientFamilyPreservation_of_control original horiginalEmbedded q hq
      originalControl horiginalUnion
  have hjointPreserved :
      Nonempty (QuotientJointPeripheralPreservation q selected original) :=
    quotientJointPeripheralPreservation_of_control selected original joint
      hbaseInv horiginal hselected q hq hjointEmbedded hjointSub
      jointControl
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
    (hjointSub : ∃ T : Set G, T.Finite ∧ joint.base ⊆ original.base ∪ T)
    (jointControl : RelativeIsoperimetricControl joint q hq) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q original
        selected.rel.alphabet.carrier) ∧
      Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hinjRelative : Set.InjOn q
      (cayleyBall selected.rel.alphabet (max R 1)) :=
    injOn_relativeBall_of_relativeDiagramCertificates selected.rel
      hsc hmu hthreshold q hker hcert
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
      originalControl hjointEmbedded hjointSub jointControl hinjAOne
      hselectedUnion
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
    (hjointSub : ∃ T : Set G, T.Finite ∧ joint.base ⊆ original.base ∪ T)
    (R : ℕ) :
    Set.InjOn (MonoidHom.id G) (cayleyBall A.alphabet R) ∧
      Nonempty (CanonicalQuotientFamilyPreservation (MonoidHom.id G) original
        selected.rel.alphabet.carrier) ∧
      Nonempty (QuotientJointPeripheralPreservation (MonoidHom.id G)
        selected original) := by
  have hid : Function.Bijective (MonoidHom.id G) :=
    ⟨Function.injective_id, Function.surjective_id⟩
  exact ⟨Function.injective_id.injOn,
    canonicalQuotientFamilyPreservation_of_bijective original horiginalEmbedded
      (MonoidHom.id G) hid selected.rel.alphabet.carrier,
    quotientJointPeripheralPreservation_of_bijective selected original joint
      hbaseInv horiginal hselected hjointEmbedded hjointSub
      (MonoidHom.id G) hid⟩

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
family and one for the source joint family.  Nothing here is new geometry: the
two constructors above do the transport, and the radius-one injectivity both
need is read off the selected assembly at radius `max R 1`.

Every landed control producer, `RelativeIsoperimetricBridgeStatement` included,
is indexed by the family that carries the relator set `W`, and here `W` is a set
of words over `RelLetter G (AuxiliaryPeripheralIndex k)`.  So the bridge applies
verbatim to the selected family, and to the other two only after the relators
are re-spelled over their letters.  That re-spelling is isolated below as
`RelatorRespellingAt`, and the two controls are then proved, not assumed.
-/

/-- **Osin's relative-isoperimetric conclusion for the two auxiliary families
of Hull Lemma 4.4.**

The quotient is Hull's: it kills the normal closure of a small-cancellation
family over the selected relative generating set.  The conclusion is the pair
of controls the family form needs, one for the original labelled family and
one for the source joint family.  No conclusion about the selected family is
asked for here; that half is already reduced.

The small-cancellation parameters are chosen by the statement, exactly as in
`HullLemma44CanonicalQuotientStatement`: Osin's constants for the two auxiliary
families depend on those families, and the relator is presented afterwards. -/
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
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
          {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Surjective q),
          RelWord.IsLemma44Input selected.rel W eps mu rho →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Nonempty (RelativeIsoperimetricControl original q hq) ∧
              Nonempty (RelativeIsoperimetricControl joint q hq)

/-! ### Re-spelling the relators over another peripheral structure -/

universe v

/-- Relabelling a relative letter along a map of index types.  Base letters are
untouched, and a component letter keeps its group element. -/
def relabelLetter {G : Type u} {Lambda : Type w} {Lambda' : Type v}
    (f : Lambda → Lambda') :
    GGT.RelLetter G Lambda → GGT.RelLetter G Lambda'
  | GGT.RelLetter.base x => GGT.RelLetter.base x
  | GGT.RelLetter.comp lam h => GGT.RelLetter.comp (f lam) h

@[simp] theorem relabelLetter_val {G : Type u} {Lambda : Type w}
    {Lambda' : Type v} (f : Lambda → Lambda')
    (a : GGT.RelLetter G Lambda) :
    (relabelLetter f a).val = a.val := by
  cases a <;> rfl

theorem map_val_relabelLetter {G : Type u} {Lambda : Type w}
    {Lambda' : Type v} (f : Lambda → Lambda')
    (word : List (GGT.RelLetter G Lambda)) :
    (word.map (relabelLetter f)).map GGT.RelLetter.val =
      word.map GGT.RelLetter.val := by
  induction word with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, relabelLetter_val, ih]

/-- Relabelling spells the same group element. -/
theorem listVal_map_relabelLetter {G : Type u} [Group G] {Lambda : Type w}
    {Lambda' : Type v} (f : Lambda → Lambda')
    (word : List (GGT.RelLetter G Lambda)) :
    GGT.RelLetter.listVal (word.map (relabelLetter f)) =
      GGT.RelLetter.listVal word := by
  show ((word.map (relabelLetter f)).map GGT.RelLetter.val).prod =
    (word.map GGT.RelLetter.val).prod
  rw [map_val_relabelLetter]

/-- The relabelled relator family. -/
def relabelWords {G : Type u} {Lambda : Type w} {Lambda' : Type v}
    (f : Lambda → Lambda') (W : Set (List (GGT.RelLetter G Lambda))) :
    Set (List (GGT.RelLetter G Lambda')) :=
  (fun word => word.map (relabelLetter f)) '' W

/-- Relabelling leaves the normally generating set of the filling unchanged. -/
theorem listVal_image_relabelWords {G : Type u} [Group G] {Lambda : Type w}
    {Lambda' : Type v} (f : Lambda → Lambda')
    (W : Set (List (GGT.RelLetter G Lambda))) :
    GGT.RelLetter.listVal '' relabelWords f W =
      GGT.RelLetter.listVal '' W := by
  ext g
  constructor
  · rintro ⟨w', hw', hval⟩
    obtain ⟨word, hword, hmap⟩ := hw'
    refine ⟨word, hword, ?_⟩
    rw [← hval, ← hmap, listVal_map_relabelLetter]
  · rintro ⟨word, hword, hval⟩
    refine ⟨word.map (relabelLetter f), ⟨word, hword, rfl⟩, ?_⟩
    rw [listVal_map_relabelLetter, hval]

/-- **Hull's relator family re-spelled over another peripheral structure.**

The re-spelled family normally generates the same subgroup, so it presents the
same quotient, and it is again a Lemma 4.4 input with parameters above the
prescribed thresholds.  The thresholds are what Osin's certificate theorem asks
of the target family, so they are given before the re-spelling is produced.

Only the normal closures are asked to agree, not the sets of spelled elements.
A relator family is closed under cyclic permutation, and a rotation spells the
conjugate of the relator by the prefix it moves; re-spelling changes those
prefixes, so the two families spell different conjugates and only their normal
closures survive.  Requiring the spelled sets themselves to agree would make
this predicate unsatisfiable for any genuine re-spelling. -/
def RelatorRespellingAt {G : Type u} [Group G] {Lambda : Type w}
    {Lambda' : Type v} (E : GGT.RelGenSet G Lambda')
    (W : Set (List (GGT.RelLetter G Lambda))) (eps0 rho0 : ℕ) (mu : ℝ) :
    Prop :=
  ∃ (W' : Set (List (GGT.RelLetter G Lambda'))) (eps rho : ℕ),
    eps0 ≤ eps ∧ rho0 ≤ rho ∧ 20 * (eps + 1) ≤ rho ∧
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W') =
          Subgroup.normalClosure (GGT.RelLetter.listVal '' W) ∧
        RelWord.IsLemma44Input E W' eps mu rho

/-- Model test: the empty relator family re-spells to the empty family at every
threshold, so the re-spelling predicate is not vacuous. -/
theorem relatorRespellingAt_empty {G : Type u} [Group G] {Lambda : Type w}
    {Lambda' : Type v} (E : GGT.RelGenSet G Lambda') (eps0 rho0 : ℕ)
    (mu : ℝ) :
    RelatorRespellingAt E (∅ : Set (List (GGT.RelLetter G Lambda)))
      eps0 rho0 mu := by
  refine ⟨(∅ : Set (List (GGT.RelLetter G Lambda'))), eps0,
    max rho0 (20 * (eps0 + 1)), le_rfl, Nat.le_max_left _ _,
    Nat.le_max_right _ _, ?_,
    RelWord.isLemma44Input_empty E eps0 mu _⟩
  rw [Set.image_empty, Set.image_empty]

/-- Model test: a family re-spells to itself once its own input meets the
thresholds. -/
theorem relatorRespellingAt_self {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (h : RelWord.IsLemma44Input D W eps mu rho) :
    RelatorRespellingAt D W eps0 rho0 mu :=
  ⟨W, eps, rho, heps, hrho, h20, rfl, h⟩

/-- A re-spelling produced by relabelling the index type.  This is the witness
the joint family is meant to use: its letters are the source letters with the
peripheral labels pushed along `Sum.inr`, so only the small-cancellation
clauses have to be re-established. -/
theorem relatorRespellingAt_of_relabel {G : Type u} [Group G]
    {Lambda : Type w} {Lambda' : Type v} (E : GGT.RelGenSet G Lambda')
    (W : Set (List (GGT.RelLetter G Lambda))) (f : Lambda → Lambda')
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (h : RelWord.IsLemma44Input E (relabelWords f W) eps mu rho) :
    RelatorRespellingAt E W eps0 rho0 mu :=
  ⟨relabelWords f W, eps, rho, heps, hrho, h20,
    congrArg Subgroup.normalClosure (listVal_image_relabelWords f W), h⟩

/-- **The one residual input of the family form.**

Hull's relator family, presented over the selected auxiliary alphabet, has a
re-spelling over the original peripheral family and over the source joint
family.  The source thresholds are chosen after the target thresholds, which is
the order Hull's construction uses: the relator is selected once all constants
are fixed.

This is strictly smaller than the control statement: no quotient, no diagram
certificate and no isoperimetric inequality occurs in it, only the combinatorial
small-cancellation clauses for two other peripheral structures. -/
def HullRelatorRespellingStatement : Prop :=
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
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
              RelatorRespellingAt original W eps0 rho0 mu ∧
                RelatorRespellingAt joint W eps0 rho0 mu

/-- **The two residual controls, proved.**  Osin's certificate theorem and his
relative-isoperimetric bridge are applied to each auxiliary family in turn,
against the re-spelled relators.  The thresholds handed to the re-spelling are
exactly the constants the certificate theorem returns for the two families, and
the bridge is then applied at those constants after one monotonicity step. -/
theorem familyInclusionRelativeControlStatement_of_greendlinger_of_isoperimetric_of_respelling
    (hgeom : RelativeGreendlingerStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, w})
    (hrespell : HullRelatorRespellingStatement.{u, w}) :
    FamilyInclusionRelativeControlStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint horiginal hjoint hinl hinr
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨epsO, rho0O, hcertO⟩ :=
    hgeom original horiginal mu hmuPos hmuSixteen
  obtain ⟨epsJ, rho0J, hcertJ⟩ := hgeom joint hjoint mu hmuPos hmuSixteen
  obtain ⟨epsS, rhoS, hres⟩ :=
    hrespell selected original joint horiginal hjoint hinl hinr mu hmuPos
      hmuThousand (max epsO epsJ) (max rho0O rho0J)
  refine ⟨epsS, rhoS, mu, hmuPos, ?_⟩
  intro W Q _ q hq hsc hker
  obtain ⟨hrespO, hrespJ⟩ := hres W hsc
  constructor
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespO
    have hepsO : epsO ≤ eps' := le_trans (Nat.le_max_left _ _) heps'
    have hrhoO : rho0O ≤ rho' := le_trans (Nat.le_max_left _ _) hrho'
    have hscO : RelWord.IsLemma44Input original W' epsO mu rho' :=
      hsc'.mono_parameters hepsO le_rfl le_rfl
    have hkerO : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsO + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsO + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram original W' R),
        Nonempty (RelativeDiagramCertificate original W' epsO mu Z) := by
      intro R Z
      exact hcertO rho' hrhoO W' R hscO Z
    exact hbridge original horiginal epsO rho' mu W' q hq hmuPos hmuThousand
      h20 hscO hkerO hcert
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespJ
    have hepsJ : epsJ ≤ eps' := le_trans (Nat.le_max_right _ _) heps'
    have hrhoJ : rho0J ≤ rho' := le_trans (Nat.le_max_right _ _) hrho'
    have hscJ : RelWord.IsLemma44Input joint W' epsJ mu rho' :=
      hsc'.mono_parameters hepsJ le_rfl le_rfl
    have hkerJ : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsJ + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsJ + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram joint W' R),
        Nonempty (RelativeDiagramCertificate joint W' epsJ mu Z) := by
      intro R Z
      exact hcertJ rho' hrhoJ W' R hscJ Z
    exact hbridge joint hjoint epsJ rho' mu W' q hq hmuPos hmuThousand
      h20 hscJ hkerJ hcert

/-- The repaired family form follows from the canonical selected-family
statement together with the two residual controls.  The requested radius is
enlarged to `max R 1`, so one application supplies both the prescribed ball
and the radius-one ball carrying every original peripheral letter. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls
    (h44 : HullLemma44CanonicalQuotientStatement.{u})
    (hcontrols : FamilyInclusionRelativeControlStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal joint hbaseInv
    hjointOriginal hjointSelected hjointEmbedded hjointSub R
  obtain ⟨epsP, rhoP, muP, hmuP, hgood⟩ := h44 selected (max R 1)
  obtain ⟨epsC, rhoC, muC, hmuC, hcontrol⟩ :=
    hcontrols selected original joint horiginal hjointEmbedded hjointOriginal
      hjointSelected
  refine ⟨max epsP epsC, max rhoP rhoC, min muP muC, lt_min hmuP hmuC, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hscP : RelWord.IsLemma44Input selected.rel W epsP muP rhoP :=
    hsc.mono_parameters (Nat.le_max_left _ _) (min_le_left _ _)
      (Nat.le_max_left _ _)
  have hscC : RelWord.IsLemma44Input selected.rel W epsC muC rhoC :=
    hsc.mono_parameters (Nat.le_max_right _ _) (min_le_right _ _)
      (Nat.le_max_right _ _)
  obtain ⟨hinjMax, hselectedPreserved⟩ := hgood W q hscP hsurj hker
  have hinjR : Set.InjOn q (cayleyBall A.alphabet R) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_left R 1))
  have hinjOne : Set.InjOn q (cayleyBall A.alphabet 1) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_right R 1))
  obtain ⟨⟨originalControl⟩, ⟨jointControl⟩⟩ :=
    hcontrol W q hsurj hscC hker
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
      hjointSub jointControl⟩

/-- **Leaf B, repaired form, from three named inputs.**  Osin's certificate
theorem and his relative-isoperimetric bridge carry the selected half and, once
the relators are re-spelled, the other two conclusions as well.  The
kernel-geodesic route of `HullSCLemma44KernelAssembly` reaches the same selected
half and is not needed here, since the bridge is required for the auxiliary
families in any case. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls
    (hgeom : RelativeGreendlingerStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, 0})
    (hrespell : HullRelatorRespellingStatement.{u, 0}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, 0} :=
  hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls
    (hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric
      hgeom hbridge)
    (familyInclusionRelativeControlStatement_of_greendlinger_of_isoperimetric_of_respelling
      hgeom hbridge hrespell)

/-- **Leaf B as Theorem C currently consumes it, from four named inputs.**  The
extra hypothesis over the repaired form is the joint-family selection input, and
by `jointAuxiliaryPeripheralEmbedding_of_familyInclusion` it cannot be avoided:
the leaf entails it. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_controls
    (hgeom : RelativeGreendlingerStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, 0})
    (hrespell : HullRelatorRespellingStatement.{u, 0})
    (hsel : JointAuxiliaryPeripheralEmbedding.{u, 0}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0} :=
  hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint hsel
    (hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls
      hgeom hbridge hrespell)

end HullSC
end GroupApproximation
