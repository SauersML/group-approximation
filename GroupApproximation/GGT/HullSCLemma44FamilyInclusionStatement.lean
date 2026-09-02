import GroupApproximation.GGT.HullSCLemma44FamilyStatement

/-!
# Hull Lemma 4.4 with an included preserved alphabet

Successive fillings keep the original finite relative generating set but may
enlarge Hull's ambient alphabet.  Hull's proof uses only that every original
letter is available in the ambient alphabet: the small-cancellation estimates
run in the latter, while quotient relative hyperbolicity is asserted for the
image of the former.

`HullLemma44CanonicalQuotientFamilyInclusionStatement` is this exact form.
Specializing inclusion to equality recovers the earlier family statement, so
all existing selected-family consumers remain consequences.

The manuscript context is `non_mf_groups_exist.tex` lines 1111--1129: the
generating set is Hull's (lines 1114--1115), and the printed theorem
(lines 1122--1129) is stated for one acylindrically hyperbolic group and one
suitable subgroup, with no peripheral family and no hyperbolic embeddedness.
The two labelled families here belong to the relatively hyperbolic refinement
used by Osin's Theorem 2.4; the source lemma is Hull's Lemma 4.4, whose
setting already fixes one hyperbolically embedded family `{H λ}` and states
the small-cancellation condition over it.

`HullLemma44CanonicalQuotientFamilyInclusionJointStatement` repairs the joint
conjunct by binding the source joint family, which the printed setting
supplies and the current statement does not.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **Hull Lemma 4.4 with an arbitrary preserved family whose alphabet is
contained in the filling alphabet.**

Manuscript: `non_mf_groups_exist.tex` lines 1122--1129 for the printed
theorem, lines 1114--1115 for the alphabet and lines 1147--1149 for the
selected witnesses.

Its fourth conjunct asserts a joint hyperbolically embedded family in the
quotient, while no hypothesis relates `selected` to `original` in the source.
That is a statement-level defect, not only a missing proof:
`jointAuxiliaryPeripheralEmbedding_of_familyInclusion` below extracts the
source joint family from this Prop alone, by taking the identity quotient and
the empty relator family.  So this Prop entails the joint-embedding theorem
(Dahmani--Guirardel--Osin Proposition 4.35 in the direction recorded as
unavailable in `RelHypOsin24CombinedFamily`) with no small-cancellation input
at all.  `HullLemma44CanonicalQuotientFamilyInclusionJointStatement` is the
repaired form, and the two are equivalent modulo exactly that extraction. -/
def HullLemma44CanonicalQuotientFamilyInclusionStatement : Prop :=
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
            RelWord.IsLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-! ## The repaired joint form -/

/-- **Hull Lemma 4.4, arbitrary preserved family, with the source joint family
bound.**

This is the previous statement with the data Hull's setting supplies and the
previous form omits: the source joint family over the sum index, its base
symmetry, the two family-agreement equations, and its hyperbolic
embeddedness.  No numerical hypothesis is added: `eps`, `rho` and
`mu` are still chosen after the families and the radius, and the
small-cancellation input is still stated over the selected relative
generating set, exactly as in the printed lemma.

The conclusion block is unchanged, and it is model-tested at the identity
quotient by `familyInclusionConclusion_identityModel` below, whose hypotheses
are precisely the new binders.  The fixed-parameter producer
`familyInclusionConclusion_of_relativeControls` takes the same four, so this
form is the one the landed assembly can reach. -/
def HullLemma44CanonicalQuotientFamilyInclusionJointStatement : Prop :=
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
        joint.base ⊆ original.base →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-- **The joint-family selection input.**

The source joint family `{H λ} ∪ {E(a_i)}` over the original relative base is
exactly what Hull's Lemma 4.4 assumes and what the repaired statement binds.
It is not produced anywhere in this repository: Hull's Theorem 3.16, proved as
`isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional`,
embeds the selected cyclic family over Hull's own alphabet, and combining it
with an ambient hyperbolically embedded family is Dahmani--Guirardel--Osin
Proposition 4.35, recorded as unavailable in `RelHypOsin24CombinedFamily`.

Nothing in the manuscript supplies it either: the printed theorem
(`non_mf_groups_exist.tex` lines 1122--1129) has no peripheral family, and the
selection sentence (lines 1147--1149) cites Hull's Corollary 5.7 and Lemma 5.8
for two suitable witnesses only. -/
def JointAuxiliaryPeripheralEmbedding : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
      original.alphabet.carrier ⊆ A.alphabet.carrier →
      original.IsHyperbolicallyEmbedded →
        ∃ joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)),
          (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) ∧
            (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) ∧
              (∀ i : AuxiliaryPeripheralIndex k,
                joint.fam (Sum.inr i) = selected.cores.peripheral i) ∧
                joint.IsHyperbolicallyEmbedded ∧
                  joint.base ⊆ original.base

/-! ## The empty relator family -/

/-- Every clause of Hull's Lemma 4.4 input quantifies over the relator family,
so the empty family satisfies all of them.  This is the instance that exposes
what the unrepaired statement asserts with no small-cancellation content. -/
theorem RelWord.isLemma44Input_empty {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (mu : ℝ) (rho : ℕ) :
    RelWord.IsLemma44Input D
      (∅ : Set (List (GGT.RelLetter G Lambda))) eps mu rho := by
  have hsupport :
      {a : GGT.RelLetter G Lambda |
        (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
          ∃ v ∈ (∅ : Set (List (GGT.RelLetter G Lambda))), a ∈ v}.Finite := by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro a ⟨-, v, hv, -⟩
    exact absurd hv (Set.notMem_empty v)
  exact
    { admissible := fun v hv => absurd hv (Set.notMem_empty v)
      inv_mem := fun v hv => absurd hv (Set.notMem_empty v)
      rotate_mem := fun v hv => absurd hv (Set.notMem_empty v)
      long := fun v hv => absurd hv (Set.notMem_empty v)
      deep := fun v hv => absurd hv (Set.notMem_empty v)
      pieces_small := fun _ v hpiece => absurd hpiece.1 (Set.notMem_empty v)
      quasiGeodesic := fun v hv => absurd hv (Set.notMem_empty v)
      publishedPiecesSmall := fun _ _ v hpiece =>
        absurd hpiece.1 (Set.notMem_empty v)
      stronglyBounded := hsupport }

/-! ## What the unrepaired statement already asserts -/

/-- The identity quotient by the empty relator family satisfies every
hypothesis of the unrepaired statement, so its joint conjunct fires there.
The output is a source joint family for `selected` and `original`. -/
theorem quotientJointPeripheralPreservation_id_of_familyInclusion
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (horiginal : original.IsHyperbolicallyEmbedded) :
    Nonempty
      (QuotientJointPeripheralPreservation (MonoidHom.id G) selected
        original) := by
  obtain ⟨eps, rho, mu, _hmu, hgood⟩ := h44 selected original hA horiginal 0
  have hker : (MonoidHom.id G).ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))) := by
    rw [MonoidHom.ker_id, Set.image_empty, Subgroup.normalClosure_empty]
  obtain ⟨-, -, -, hjoint⟩ :=
    hgood (∅ : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
      (MonoidHom.id G)
      (RelWord.isLemma44Input_empty selected.rel eps mu rho)
      Function.surjective_id hker
  exact hjoint

/-- **The unrepaired statement contains the joint-family selection input.**
No relator, no quotient and no small-cancellation hypothesis is used. -/
theorem jointAuxiliaryPeripheralEmbedding_of_familyInclusion
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w}) :
    JointAuxiliaryPeripheralEmbedding.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal
  obtain ⟨P⟩ := quotientJointPeripheralPreservation_id_of_familyInclusion h44
    selected original hA horiginal
  refine ⟨P.rel, P.base_inv, ?_, ?_, P.embedded, ?_⟩
  · intro x hx
    have hmem := P.base_subset hx
    rwa [Set.image_id] at hmem
  · intro lam
    rw [P.fam_original lam, Subgroup.map_id]
  · intro i
    rw [P.fam_selected i, Subgroup.map_id]

/-- The repaired form is weaker: it is the same conclusion under strictly more
hypotheses. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_familyInclusion
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal _ _ _ _ _ _ R
  exact h44 selected original hA horiginal R

/-- **The exact difference between the two forms.**  Together with
`jointAuxiliaryPeripheralEmbedding_of_familyInclusion` and
`hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_familyInclusion`
this says the unrepaired statement is equivalent to the repaired one
conjoined with the joint-family selection input. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (hsel : JointAuxiliaryPeripheralEmbedding.{u, w})
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal R
  obtain ⟨joint, hbaseInv, hjointOriginal, hjointSelected, hjointEmbedded,
    hjointSub⟩ := hsel selected original hA horiginal
  exact h44 selected original hA horiginal joint hbaseInv hjointOriginal
    hjointSelected hjointEmbedded hjointSub R

/-- The inclusion form specializes directly to the established canonical
selected-family statement by preserving the empty original family. -/
theorem hullLemma44CanonicalQuotientStatement_of_familyInclusion
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
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

/-- The repaired form keeps Hull's selected-family route, through the same
selection input. -/
theorem hullLemma44CanonicalQuotientStatement_of_familyInclusionJoint
    (hsel : JointAuxiliaryPeripheralEmbedding.{u, 0})
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} :=
  hullLemma44CanonicalQuotientStatement_of_familyInclusion
    (hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint hsel h44)

/-! ## Identity model -/

/-- The four conclusions of the inclusion interface are simultaneously
satisfied by the identity quotient whenever the source joint family is
hyperbolically embedded.  This tests the arbitrary-family output independently
of the small-cancellation threshold quantifiers. -/
theorem familyInclusionConclusion_identityModel
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (horiginal : original.IsHyperbolicallyEmbedded)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (hjointOriginal : ∀ lam,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hjointSelected : ∀ i,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (hjoint : joint.IsHyperbolicallyEmbedded)
    (hjointSub : joint.base ⊆ original.base) (R : ℕ) :
    Set.InjOn (MonoidHom.id G) (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation (MonoidHom.id G) selected) ∧
      Nonempty
        (CanonicalQuotientFamilyPreservation (MonoidHom.id G) original) ∧
      Nonempty
        (QuotientJointPeripheralPreservation (MonoidHom.id G) selected
          original) := by
  have hid : Function.Bijective (MonoidHom.id G) :=
    ⟨Function.injective_id, Function.surjective_id⟩
  exact ⟨Function.injective_id.injOn,
    quotientPeripheralPreservation_of_bijective selected (MonoidHom.id G) hid,
    canonicalQuotientFamilyPreservation_of_bijective original horiginal
      (MonoidHom.id G) hid,
    quotientJointPeripheralPreservation_of_bijective selected original joint
      hbaseInv hjointOriginal hjointSelected hjoint hjointSub
      (MonoidHom.id G) hid⟩

end HullSC
end GroupApproximation
