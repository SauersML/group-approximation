import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.DGOProposition435JointPrescribed
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 4.4 statements over strongly bounded relator families

The four Hull leaves of Theorem C feed Hull's Lemma 4.4 through Osin's Lemma 5.1,
and Lemma 5.1 is a theorem about **finite** relator families: its bridge in the
form consumers read, `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`
(`GGT/HullSCLemma51EmbeddedBridge.lean`), asks for the published strong
boundedness `RelWord.IsBoundedLemma44Input`.  The canonical statements above
it quantify over every family with the historical `RelWord.IsLemma44Input`,
which omits the length bound, so they cannot be fed from that bridge.

This module restates them with the bounded input:
`BoundedHullLemma44CanonicalQuotientStatement`,
`BoundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement`,
`BoundedHullLemma44CanonicalQuotientFamilyInclusionStatement`, the re-spelling
`BoundedHullRelatorRespellingStatement`, and the family control in the form its
consumers read, `BoundedFamilyInclusionRelativeEmbeddingStatement`.

Nothing is lost at the producer end.  The canonical quotient uses the
symmetrized closure of one relator, which is bounded
(`RelWord.IsLemma44Input.bounded_symmetrized`), so
`torsionFreeHullCanonicalQuotientStatement_of_boundedLemma44_of_lemma49`
recovers `TorsionFreeHullCanonicalQuotientStatement` verbatim, and
`boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesic` produces the
bounded canonical statement from the certificate theorem and the embedded bridge
alone.  The family form's combinators are in
`GGT/HullSCLemma44BoundedFamilyBridge.lean`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The bounded statements -/

/-- **Hull Lemma 4.4, canonical selected-family form, over strongly bounded
families.**  `HullLemma44CanonicalQuotientStatement` with the published
bounded input. -/
def BoundedHullLemma44CanonicalQuotientStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    (R : ℕ),
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
          {Q : Type u} [Group Q] (q : G →* Q),
          RelWord.IsBoundedLemma44Input D.rel W eps mu rho →
          Function.Surjective q →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Set.InjOn q (cayleyBall A.alphabet R) ∧
              Nonempty (QuotientPeripheralPreservation q D)

/-- `RelatorRespellingAt` with the re-spelled family strongly bounded. -/
def BoundedRelatorRespellingAt {G : Type u} [Group G] {Lambda : Type w}
    {Lambda' : Type v} (E : GGT.RelGenSet G Lambda')
    (W : Set (List (GGT.RelLetter G Lambda))) (eps0 rho0 : ℕ) (mu : ℝ) :
    Prop :=
  ∃ (W' : Set (List (GGT.RelLetter G Lambda'))) (eps rho : ℕ),
    eps0 ≤ eps ∧ rho0 ≤ rho ∧ 20 * (eps + 1) ≤ rho ∧
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W') =
          Subgroup.normalClosure (GGT.RelLetter.listVal '' W) ∧
        RelWord.IsBoundedLemma44Input E W' eps mu rho

/-- A bounded re-spelling is a re-spelling. -/
theorem BoundedRelatorRespellingAt.toRelatorRespellingAt
    {G : Type u} [Group G] {Lambda : Type w} {Lambda' : Type v}
    {E : GGT.RelGenSet G Lambda'} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps0 rho0 : ℕ} {mu : ℝ} (h : BoundedRelatorRespellingAt E W eps0 rho0 mu) :
    RelatorRespellingAt E W eps0 rho0 mu := by
  obtain ⟨W', eps, rho, heps, hrho, h20, hclosure, hsc⟩ := h
  exact ⟨W', eps, rho, heps, hrho, h20, hclosure, hsc.toIsLemma44Input⟩

/-- **Hull's §6 re-spelling over strongly bounded families.**
`HullRelatorRespellingStatement` with the bounded input and bounded outputs. -/
def BoundedHullRelatorRespellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
            RelWord.IsBoundedLemma44Input selected.rel W eps mu rho →
              BoundedRelatorRespellingAt original W eps0 rho0 mu ∧
                BoundedRelatorRespellingAt joint W eps0 rho0 mu

/-- **The two auxiliary controls of the family form, in the form their consumers
read.**  `FamilyInclusionRelativeControlStatement` with the bounded input, and
with hyperbolic embeddedness of the two image families as the conclusion: the
consumers `canonicalQuotientFamilyPreservation_of_control` and
`quotientJointPeripheralPreservation_of_control` read nothing else of a
control. -/
def BoundedFamilyInclusionRelativeEmbeddingStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
          {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Surjective q),
          RelWord.IsBoundedLemma44Input selected.rel W eps mu rho →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            (original.mapSurjective q hq).IsHyperbolicallyEmbedded ∧
              (joint.mapSurjective q hq).IsHyperbolicallyEmbedded

/-- **Hull Lemma 4.4, repaired joint family form, over strongly bounded
families.**  `HullLemma44CanonicalQuotientFamilyInclusionJointStatement` with the
bounded input. -/
def BoundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
      original.alphabet.carrier ⊆ A.alphabet.carrier →
      original.IsHyperbolicallyEmbedded →
      ∀ joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)),
        (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) →
        (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
        (∀ i : AuxiliaryPeripheralIndex k,
          joint.fam (Sum.inr i) = selected.cores.peripheral i) →
        joint.IsHyperbolicallyEmbedded →
        (∃ T : Set G, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧
          joint.base ⊆ original.base ∪ T) →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsBoundedLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original
                  selected.rel.alphabet.carrier) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-- **Hull Lemma 4.4, family form, over strongly bounded families.**
`HullLemma44CanonicalQuotientFamilyInclusionStatement` with the bounded input. -/
def BoundedHullLemma44CanonicalQuotientFamilyInclusionStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
      original.alphabet.carrier ⊆ A.alphabet.carrier →
      original.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsBoundedLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original
                  selected.rel.alphabet.carrier) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-! ## Forgetting the bound -/

/-- The unbounded canonical statement implies the bounded one. -/
theorem boundedHullLemma44CanonicalQuotientStatement_of_unbounded
    (h : HullLemma44CanonicalQuotientStatement.{u}) :
    BoundedHullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h D R
  exact ⟨eps, rho, mu, hmu, fun W Q _ q hsc hsurj hker =>
    hgood W q hsc.toIsLemma44Input hsurj hker⟩

/-! ## Transport from embeddedness -/

/-- `canonicalQuotientFamilyPreservation_of_control`, reading only what it
uses: hyperbolic embeddedness of the image family. -/
theorem canonicalQuotientFamilyPreservation_of_embedded
    {G : Type u} [Group G] {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hembedded : (original.mapSurjective q hq).IsHyperbolicallyEmbedded)
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
    embedded := hembedded
    injOn_peripheralUnion := hinj }⟩

/-- `quotientJointPeripheralPreservation_of_control`, reading only what it
uses: hyperbolic embeddedness of the image joint family. -/
theorem quotientJointPeripheralPreservation_of_embedded
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
    (hjointSub : ∃ T : Set G, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧
      joint.base ⊆ original.base ∪ T)
    (hjointQ : (joint.mapSurjective q hq).IsHyperbolicallyEmbedded) :
    Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  refine ⟨{
    rel := joint.mapSurjective q hq
    base_inv := ?_
    fam_original := ?_
    fam_selected := ?_
    embedded := hjointQ
    base_subset := by
      obtain ⟨T, hT, hTY, hsub⟩ := hjointSub
      exact ⟨T, hT, hTY, Set.image_mono hsub⟩ }⟩
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

/-! ## The canonical statement from the certificate theorem and the bridge -/

/-- **Hull's bounded canonical quotient statement from the two source-faithful
inputs.**  `hullLemma44CanonicalQuotientStatement_of_quasiGeodesic` with the
bounded input and the embedded bridge; every numerical choice is the
original's. -/
theorem boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesic
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, u, 0}) :
    BoundedHullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨eps, rho₀, hcertificate⟩ :=
    hgeom D.rel D.embedded mu hmuPos hmuSixteen
  let fullRadius : ℕ := max R 1
  let boundaryScale : ℕ := 2 * fullRadius + 2 * eps + 1
  let rho : ℕ := max rho₀ (max (8 * boundaryScale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale, fullRadius]
    positivity
  have hrhoScaleReal :
      (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D.rel W eps mu Z) := by
    intro r Z hZ
    exact hcertificate rho hrho₀ W r hsc.toIsLemma44Input Z hZ
  have hAlphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier := by
    intro x hx
    exact Set.mem_union_left _ (D.base_le hx)
  have hinject :=
    injOn_ball_and_peripheralUnion_of_quasiGeodesicCertificates
      D.rel A.alphabet hAlphabet hsc.toIsLemma44Input hmuNinetyTwo hthreshold
        q hker (hcert (max R 1))
  have hinjectCores : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    apply hinject.2
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · exact hxy
  refine ⟨hinject.1, ?_⟩
  exact quotientPeripheralPreservation_of_embeddedBridge hbridge D q hsurj
    hmuPos hmuThousand hrhoDehn hsc hker hcert hinjectCores

/-! ## The torsion-free canonical quotient from the bounded statement -/

/-- **`TorsionFreeHullCanonicalQuotientStatement` from the bounded canonical
statement.**  `torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49`
verbatim: its Lemma 4.4 input is the symmetrized closure of one relator, whose
length bound is `RelWord.IsLemma44Input.bounded_symmetrized`. -/
theorem torsionFreeHullCanonicalQuotientStatement_of_boundedLemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : BoundedHullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    TorsionFreeHullCanonicalQuotientStatement.{u} := by
  intro G _ hG A N hN k S hS t R
  obtain ⟨D₀⟩ := hselect A S hN hS
  obtain ⟨D, ht, hacy⟩ := D₀.exists_acylindricalAdjoinPair t
  obtain ⟨eps44, rho44, mu44, hmu44, hgood44⟩ := h44 D R
  obtain ⟨eps49, rho49, mu49, hmu49, hgood49⟩ :=
    h49 D.rel D.embedded hacy
  refine ⟨D, max eps44 eps49, max rho44 rho49, min mu44 mu49,
    ht, lt_min hmu44 hmu49, ?_⟩
  intro W v hv hsc
  let K : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  let Q : Type u := G ⧸ K
  let q : G →* Q := QuotientGroup.mk' K
  have hscV : RelWord.IsLemma49Input D.rel (RelWord.symmetrized v)
      (max eps44 eps49) (min mu44 mu49) (max rho44 rho49) :=
    hsc.restrict_symmetrized hv
  have hsc44 : RelWord.IsBoundedLemma44Input D.rel (RelWord.symmetrized v)
      eps44 mu44 rho44 :=
    (hscV.toIsLemma44Input.mono_parameters
      (Nat.le_max_left _ _) (min_le_left _ _)
        (Nat.le_max_left _ _)).bounded_symmetrized
  have hsc49 : RelWord.IsLemma49Input D.rel W eps49 mu49 rho49 :=
    hsc.mono_parameters
      (Nat.le_max_right _ _) (min_le_right _ _) (Nat.le_max_right _ _)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hker : q.ker = K := QuotientGroup.ker_mk' K
  have hkerV : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
    rw [hker, RelWord.normalClosure_listVal_image_symmetrized]
  obtain ⟨hinj, ⟨P⟩⟩ := hgood44 (RelWord.symmetrized v) q hsc44 hsurj hkerV
  have hpower : KernelPowerCorrection K := hgood49 W v hv hsc49
  have hlift : ∀ y : Q, IsOfFinOrder y →
      ∃ g : G, q g = y ∧ orderOf g = orderOf y := by
    apply (kernelPowerCorrection_iff_finiteOrderLift q hsurj).mp
    rwa [hker]
  have hQ : IsPowerTorsionFree Q :=
    torsionFree_of_finiteOrder_lift hG q hlift
  obtain ⟨F⟩ := nonempty_fillingAlphabetData_of_peripheralPreservation hQ D P
  exact ⟨{ Q := Q
           group := inferInstance
           q := q
           surjective := hsurj
           ker_eq := hker
           hullSet := F.hullSet
           alphabet_image := F.alphabet_image
           injOn := hinj
           suitable_map := F.suitable_map
           suitable_map_family := F.suitable_map_family
           finiteOrder_lift := hlift }⟩

/-! ## The selected-family statement from the family form -/

/-- The bounded family form specializes to the bounded canonical statement by
preserving the empty original family. -/
theorem boundedHullLemma44CanonicalQuotientStatement_of_familyInclusion
    (h44 : BoundedHullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0}) :
    BoundedHullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S selected R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 selected (emptyPreservedRelGenSet A)
      (by rw [emptyPreservedRelGenSet_alphabet A])
      (emptyPreservedRelGenSet_embedded A) R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, hselected, _horiginal, _hjoint⟩ :=
    hgood W q hinput hsurj hker
  exact ⟨hinj, hselected⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.BoundedRelatorRespellingAt.toRelatorRespellingAt
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_unbounded
#audit_axioms GroupApproximation.HullSC.canonicalQuotientFamilyPreservation_of_embedded
#audit_axioms GroupApproximation.HullSC.quotientJointPeripheralPreservation_of_embedded
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesic
#audit_axioms GroupApproximation.HullSC.torsionFreeHullCanonicalQuotientStatement_of_boundedLemma44_of_lemma49
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_familyInclusion
