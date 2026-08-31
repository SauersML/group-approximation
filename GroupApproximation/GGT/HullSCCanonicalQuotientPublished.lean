import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.GGT.HullSCLemma44ReducedDiagram
import GroupApproximation.GGT.HullSCRelatorSeparation2PublishedReduction
import GroupApproximation.GGT.RelGenSetMulEquiv
import GroupApproximation.GroupTheory.FiniteRelatorQuotient

/-!
# Hull's published quotient through the canonical relator quotient

Hull's Lemmas 4.4 and 4.9 concern the natural quotient by the relators.  They
do not construct a cone-off, a rotating family, or an application of DGO
Theorem 5.3.  This file records their actual outputs and assembles the quotient
used in the torsion-free manuscript lane directly as
`G ⨸ normalClosure {w}`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

/-- The values of a one-relator symmetrized family normally generate exactly
the same subgroup as the value of the original relator. -/
theorem normalClosure_listVal_image_symmetrized
    {G : Type u} [Group G] {Λ : Type w}
    (v : List (GGT.RelLetter G Λ)) :
    Subgroup.normalClosure (GGT.RelLetter.listVal '' symmetrized v) =
      Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc | hc⟩ := Sym.exists_conj (mem_symmetrized.mp hz)
    · rw [hc]
      change c⁻¹ * GGT.RelLetter.listVal v * c ∈
        Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
      simpa only [inv_inv] using
        (Subgroup.normalClosure_normal
          (s := ({GGT.RelLetter.listVal v} : Set G))).conj_mem
            (GGT.RelLetter.listVal v)
            (Subgroup.subset_normalClosure rfl) c⁻¹
    · rw [hc]
      change c⁻¹ * (GGT.RelLetter.listVal v)⁻¹ * c ∈
        Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
      simpa only [inv_inv] using
        (Subgroup.normalClosure_normal
          (s := ({GGT.RelLetter.listVal v} : Set G))).conj_mem
            (GGT.RelLetter.listVal v)⁻¹
            ((Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G)).inv_mem
                (Subgroup.subset_normalClosure rfl)) c⁻¹
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subgroup.subset_normalClosure
      ⟨v, self_mem_symmetrized v, rfl⟩

end RelWord

/-- Hull Lemma 4.4 in the exact form needed after the simultaneous auxiliary
peripherals have been selected: ball injectivity and preservation of that
peripheral family in any natural quotient by the relator family. -/
def HullLemma44CanonicalQuotientStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    (R : ℕ),
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
          {Q : Type u} [Group Q] (q : G →* Q),
          RelWord.IsLemma44Input D.rel W eps mu rho →
          Function.Surjective q →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Set.InjOn q (cayleyBall A.alphabet R) ∧
              Nonempty (QuotientPeripheralPreservation q D)

/-- Hull Lemma 4.9 reduced to its quotient-free diagram conclusion, for an
arbitrary hyperbolically embedded source family. -/
def HullLemma49KernelPowerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            KernelPowerCorrection (Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G))

/-! ## The zero-relator case of Lemma 4.4 -/

/-- A bijective quotient map transports the selected relative generating set
literally, so every peripheral and its relative metric are preserved. -/
theorem quotientPeripheralPreservation_of_bijective
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Bijective q) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  let e : G ≃* Q := MulEquiv.ofBijective q hq
  refine ⟨{ rel := D.rel.mapMulEquiv e,
             base_image := ?_,
             fam_map := ?_,
             embedded := D.embedded.mapMulEquiv e,
             injOn_peripheralUnion := hq.1.injOn }⟩
  · intro a ha
    change q a ∈ q '' D.rel.base
    exact ⟨a, D.base_eq ▸ ha, rfl⟩
  · intro i
    change (D.rel.fam i).map q = (D.cores.peripheral i).map q
    rw [D.fam_eq i]

/-- The conclusion of Hull Lemma 4.4 for the empty relator family.  Its normal
closure is trivial, hence the given quotient map is injective; the preceding
isomorphism transport supplies the complete quotient peripheral record. -/
theorem hullLemma44Canonical_empty
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    (R : ℕ) {Q : Type u} [Group Q] (q : G →* Q)
    (hsurj : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))))) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation q D) := by
  have hbot : q.ker = ⊥ := by
    simpa using hker
  have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hbot
  exact ⟨hinj.injOn,
    quotientPeripheralPreservation_of_bijective D q ⟨hinj, hsurj⟩⟩

/-- The corrected quotient half of Hull's construction in the torsion-free
lane.  The auxiliary family is chosen before the relator, so Lemma 4.4 really
does preserve every subgroup whose image must remain suitable. -/
def TorsionFreeHullCanonicalQuotientStatement : Prop :=
  ∀ {G : Type u} [Group G], IsPowerTorsionFree G →
    ∀ (A : HullGeneratingSet G) (N : Subgroup G),
      Suitable A.alphabet N →
        ∀ {k : ℕ} (S : Fin k → Subgroup G),
          (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
            ∃ (D : AuxiliaryPeripheralFamily A N S)
              (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
                ∀ (W : Set
                    (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
                  (v : List
                    (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
                  v ∈ W → RelWord.IsLemma49Input D.rel W eps mu rho →
                    Nonempty (HullFillingQuotient A N S
                      (GGT.RelLetter.listVal v) R)

/-- Exact assembly of the canonical quotient.  Parameter synchronisation is
the only small-cancellation bookkeeping; the quotient group and map are the
literal quotient by the singleton relator, Lemma 4.4 supplies injectivity and
peripheral preservation, Lemma 5.8 supplies the common quotient alphabet, and
Lemma 4.9 supplies both torsion-freeness and the order-preserving lift. -/
theorem torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : HullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    TorsionFreeHullCanonicalQuotientStatement.{u} := by
  intro G _ hG A N hN k S hS R
  obtain ⟨D⟩ := hselect A S hN hS
  obtain ⟨eps44, rho44, mu44, hmu44, hgood44⟩ := h44 D R
  obtain ⟨eps49, rho49, mu49, hmu49, hgood49⟩ := h49 D.rel D.embedded
  refine ⟨D, max eps44 eps49, max rho44 rho49, min mu44 mu49,
    lt_min hmu44 hmu49, ?_⟩
  intro W v hv hsc
  let V := RelWord.symmetrized v
  let K : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  let Q : Type u := G ⧸ K
  let q : G →* Q := QuotientGroup.mk' K
  have hscV : RelWord.IsLemma49Input D.rel V
      (max eps44 eps49) (min mu44 mu49) (max rho44 rho49) :=
    hsc.restrict_symmetrized hv
  have hsc44 : RelWord.IsLemma44Input D.rel V eps44 mu44 rho44 :=
    hscV.toIsLemma44Input.mono_parameters
      (Nat.le_max_left _ _) (min_le_left _ _) (Nat.le_max_left _ _)
  have hsc49 : RelWord.IsLemma49Input D.rel W eps49 mu49 rho49 :=
    hsc.mono_parameters
      (Nat.le_max_right _ _) (min_le_right _ _) (Nat.le_max_right _ _)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hker : q.ker = K := QuotientGroup.ker_mk' K
  have hkerV : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' V) := by
    rw [hker, RelWord.normalClosure_listVal_image_symmetrized]
  obtain ⟨hinj, ⟨P⟩⟩ := hgood44 V q hsc44 hsurj hkerV
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

end HullSC
end GroupApproximation
