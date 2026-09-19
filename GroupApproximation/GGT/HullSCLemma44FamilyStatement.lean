import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet
import GroupApproximation.GGT.OsinTheorem54SepSymmetric

/-!
# Hull Lemma 4.4 with an arbitrary preserved peripheral family

Hull's relator is written over the finitely many selected elementary closures.
In the relatively hyperbolic specialization there is also an arbitrary
original peripheral family.  Lemma 4.4 preserves both through the same natural
quotient.

Two quotient views are needed and are stated separately:

* `CanonicalQuotientFamilyPreservation` is the image of the original relative
  structure.  Its base is exactly `q '' X`, so a finite Osin base stays finite.
* `QuotientJointPeripheralPreservation` places the mapped original peripherals
  and mapped selected elementary closures in one hyperbolically embedded
  labelled family.  This is the input to almost-malnormality when proving that
  the mapped suitable witnesses remain non-parabolic and non-commensurable.

The selected family is also returned through the existing
`QuotientPeripheralPreservation`, so all established Hull consumers keep their
current interface.  Specializing the arbitrary original family to the empty
family proves `HullLemma44CanonicalQuotientStatement`.

The identity-quotient constructors and the empty-relator theorem are model
tests for the three simultaneous preservation records.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Original-family preservation -/

/-- The canonical quotient image of the original labelled peripheral family. -/
structure CanonicalQuotientFamilyPreservation
    {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
    (q : G →* Q) (D : GGT.RelGenSet G Lambda) (Y : Set G) where
  rel : GGT.RelGenSet Q Lambda
  /-- The quotient relative base is the image of the source base together with
  finitely many extra letters drawn from `Y`.  Osin's Theorem 2.4 outputs the
  image of the source base; the finite enlargement is what the printed
  Proposition 4.35 adjoins when it drops the auxiliary members. -/
  base_map : ∃ T : Set G, T.Finite ∧ T ⊆ Y ∧ rel.base ⊆ q '' (D.base ∪ T)
  fam_map : ∀ lam : Lambda, rel.fam lam = (D.fam lam).map q
  embedded : rel.IsHyperbolicallyEmbedded
  injOn_peripheralUnion :
    Set.InjOn q (⋃ lam : Lambda, (D.fam lam : Set G))

namespace CanonicalQuotientFamilyPreservation

variable {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
  {q : G →* Q} {D : GGT.RelGenSet G Lambda} {Y : Set G}

theorem injOn_fam (P : CanonicalQuotientFamilyPreservation q D Y)
    (lam : Lambda) : Set.InjOn q (D.fam lam : Set G) := by
  intro x hx y hy hxy
  exact P.injOn_peripheralUnion
    (Set.mem_iUnion.mpr ⟨lam, hx⟩)
    (Set.mem_iUnion.mpr ⟨lam, hy⟩) hxy

theorem base_finite (P : CanonicalQuotientFamilyPreservation q D Y)
    (hfinite : D.base.Finite) : P.rel.base.Finite := by
  obtain ⟨T, hT, -, hsub⟩ := P.base_map
  exact (((hfinite.union hT).image q)).subset hsub

/-- The preserved relative alphabet lies in the image of the source relative
alphabet together with the allowed enlargement.  Only this inclusion survives
the weakening of `base_map`; the reverse needed `q '' D.base ⊆ rel.base`. -/
theorem alphabet_carrier_subset_image
    (P : CanonicalQuotientFamilyPreservation q D Y) :
    P.rel.alphabet.carrier ⊆ q '' (D.alphabet.carrier ∪ Y) := by
  obtain ⟨T, -, hTY, hsub⟩ := P.base_map
  rintro y (hy | hy)
  · obtain ⟨x, hx, rfl⟩ := hsub hy
    rcases hx with hx | hx
    · exact ⟨x, Or.inl (Set.mem_union_left _ hx), rfl⟩
    · exact ⟨x, Or.inr (hTY hx), rfl⟩
  · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
    rw [P.fam_map lam] at hlam
    obtain ⟨x, hx, rfl⟩ := hlam
    exact ⟨x, Or.inl (Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨lam, hx⟩)), rfl⟩

end CanonicalQuotientFamilyPreservation

/-! ## Joint original-and-selected preservation -/

/-- The mapped original family and selected elementary closures in one
labelled hyperbolically embedded family. -/
structure QuotientJointPeripheralPreservation
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Lambda : Type w}
    {Q : Type u} [Group Q] (q : G →* Q)
    (selected : AuxiliaryPeripheralFamily A N S)
    (original : GGT.RelGenSet G Lambda) where
  rel : GGT.RelGenSet Q (Sum Lambda (AuxiliaryPeripheralIndex k))
  base_inv : ∀ x ∈ rel.base, x⁻¹ ∈ rel.base
  fam_original : ∀ lam : Lambda,
    rel.fam (Sum.inl lam) = (original.fam lam).map q
  fam_selected : ∀ i : AuxiliaryPeripheralIndex k,
    rel.fam (Sum.inr i) = (selected.cores.peripheral i).map q
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The joint relative base comes from the original one, enlarged by finitely
  many letters of the selected relative alphabet.  Relative hyperbolicity of the
  quotient with respect to the original family asks for a finite relative
  generating set, and Proposition 4.35 in its printed direction builds one from
  this base by adjoining finitely many generators of the members it drops; so
  this base has to be finite, and it is, because the original base is.  The
  enlargement is confined to the selected relative alphabet, which is what
  `CanonicalQuotientFamilyPreservation.base_map` asks of its own enlargement. -/
  base_subset : ∃ T : Set G, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧
    rel.base ⊆ q '' (original.base ∪ T)

namespace QuotientJointPeripheralPreservation

/-- The joint quotient base is finite whenever the original relative base is,
which is the form Proposition 4.35's printed direction consumes. -/
theorem base_finite {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G} {Lambda : Type w}
    {Q : Type u} [Group Q] {q : G →* Q}
    {selected : AuxiliaryPeripheralFamily A N S}
    {original : GGT.RelGenSet G Lambda}
    (P : QuotientJointPeripheralPreservation q selected original)
    (hfinite : original.base.Finite) : P.rel.base.Finite := by
  obtain ⟨T, hT, -, hsub⟩ := P.base_subset
  exact (((hfinite.union hT).image q)).subset hsub

end QuotientJointPeripheralPreservation

/-- The enlargement clause is automatic once the joint relative base lies in
the selected one: intersecting a finite enlargement with the joint base keeps
it finite, confines it to the selected relative alphabet, and still covers the
joint base. -/
theorem exists_finite_adjoin_within_alphabet
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} {original : GGT.RelGenSet G Lambda}
    {joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))}
    (hwithin : joint.base ⊆ selected.rel.base)
    (hsub : ∃ T : Set G, T.Finite ∧ joint.base ⊆ original.base ∪ T) :
    ∃ T : Set G, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧
      joint.base ⊆ original.base ∪ T := by
  obtain ⟨T, hT, hTsub⟩ := hsub
  refine ⟨T ∩ joint.base, hT.inter_of_left _, ?_, ?_⟩
  · intro x hx
    show x ∈ selected.rel.base ∪
      ⋃ i : AuxiliaryPeripheralIndex k,
        ((selected.rel.fam i : Subgroup G) : Set G)
    exact Set.mem_union_left _ (hwithin hx.2)
  · intro x hx
    rcases hTsub hx with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ ⟨h, hx⟩

/-! ## The arbitrary-family statement -/

/-- **Hull Lemma 4.4, arbitrary preserved-family canonical form.**

The original relative Cayley alphabet is Hull's fixed alphabet.  The relators
remain words over the selected auxiliary family.  The conclusion preserves the
selected family, the canonical original finite-base structure, and their joint
labelled family in the same quotient. -/
def HullLemma44CanonicalQuotientFamilyStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
      original.alphabet = A.alphabet →
      original.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original
                  selected.rel.alphabet.carrier) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-! ## Identity models -/

theorem canonicalQuotientFamilyPreservation_of_bijective
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Bijective q)
    (Y : Set G) :
    Nonempty (CanonicalQuotientFamilyPreservation q D Y) := by
  refine ⟨{
    rel := D.mapSurjective q hq.2
    base_map := ⟨∅, Set.finite_empty, Set.empty_subset Y, by
      intro y hy
      rw [Set.union_empty]
      exact hy⟩
    fam_map := fun _ => rfl
    embedded := GGT.RelGenSet.isHyperbolicallyEmbedded_mapSurjective_of_bijective
      D hD q hq
    injOn_peripheralUnion := hq.1.injOn }⟩

/-- A bijection transports a supplied joint source family.  The source
equalities make this a model for the two labelled halves of the output. -/
theorem quotientJointPeripheralPreservation_of_bijective
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam, joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i, joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (hjoint : joint.IsHyperbolicallyEmbedded)
    (hbaseSub : ∃ T : Set G, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧
      joint.base ⊆ original.base ∪ T)
    {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Bijective q) :
    Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  refine ⟨{
    rel := joint.mapSurjective q hq.2
    base_inv := ?_
    fam_original := ?_
    fam_selected := ?_
    embedded := GGT.RelGenSet.isHyperbolicallyEmbedded_mapSurjective_of_bijective
      joint hjoint q hq
    base_subset := by
      obtain ⟨T, hT, hTY, hsub⟩ := hbaseSub
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

/-! ## Empty original family and specialization -/

def emptyPreservedRelGenSet {G : Type u} [Group G]
    (A : HullGeneratingSet G) : GGT.RelGenSet G Empty where
  base := A.alphabet.carrier
  fam := Empty.elim
  symmetricGenerating := by
    simpa using A.alphabet.symmetricGenerating

theorem emptyPreservedRelGenSet_alphabet {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    (emptyPreservedRelGenSet A).alphabet = A.alphabet := by
  apply GGT.OsinComponents.alphabet_eq_of_carrier_eq
  show A.alphabet.carrier ∪
      ⋃ lam : Empty, ((Empty.elim lam : Subgroup G) : Set G) =
        A.alphabet.carrier
  rw [Set.iUnion_of_empty, Set.union_empty]

theorem emptyPreservedRelGenSet_embedded {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    (emptyPreservedRelGenSet A).IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [emptyPreservedRelGenSet_alphabet A]
    exact ⟨A.delta, A.hyperbolic⟩
  · intro lam
    exact Empty.elim lam

/-- The arbitrary-family statement implies the established selected-family
canonical statement by preserving the empty original family. -/
theorem hullLemma44CanonicalQuotientStatement_of_family
    (h44 : HullLemma44CanonicalQuotientFamilyStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S selected R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 selected (emptyPreservedRelGenSet A)
      (emptyPreservedRelGenSet_alphabet A)
      (emptyPreservedRelGenSet_embedded A) R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, hselected, _horiginal, _hjoint⟩ :=
    hgood W q hinput hsurj hker
  exact ⟨hinj, hselected⟩

end HullSC
end GroupApproximation
