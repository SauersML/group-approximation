import GroupApproximation.GGT.HullSCQuotientSuitabilityWithTorsion
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCTheorem51
import GroupApproximation.GGT.HullSC
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 at every acylindrically hyperbolic group

`thm:hull` is printed for every acylindrically hyperbolic `G`.  The landed chain
(`HullSC.HullOneStepStatement`, `HullTowerStatement`,
`TorsionFreeHullCanonicalQuotientStatement`) carries `IsPowerTorsionFree G`, and
its only essential use is clause (d) over the quotient: that the image of a
suitable subgroup normalizes no nontrivial finite subgroup.  That clause is now
proved over any quotient with peripheral preservation
(`nonempty_fillingAlphabetData_of_peripheralPreservation_general`).  Every other
use was a convenience, and this module restates the chain without the binder:

* `HullCanonicalQuotientStatementGeneral`, assembled from Lemmas 4.4 and 4.9;
* `HullOneStepStatementGeneral`, the one-relator quotient;
* `HullTowerStatementGeneral`, the induction on the number of targets, with
  clause (d) carrying the next step;
* `HullBallFormStatementGeneral`, Hull's published injectivity-radius form with
  the kernel datum.

Clause (e), lifting finite order with its order, was already torsion-agnostic
(`kernelPowerCorrection_iff_finiteOrderLift`).  The bounded Lemma 4.4 assembly
is `HullSCTheorem71GeneralBounded`; the least-area leaves are
`HullSCTheorem71GeneralLeastArea`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## The canonical quotient -/

/-- **The quotient half of Hull's construction, at every ambient group.**
`TorsionFreeHullCanonicalQuotientStatement` without the torsion-freeness
binder. -/
def HullCanonicalQuotientStatementGeneral : Prop :=
  ∀ {G : Type u} [Group G],
    ∀ (A : HullGeneratingSet G) (N : Subgroup G),
      Suitable A.alphabet N →
        ∀ {k : ℕ} (S : Fin k → Subgroup G),
          (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ (t : G) (R : ℕ),
            ∃ (D : AuxiliaryPeripheralFamily A N S)
              (eps rho : ℕ) (mu : ℝ), t⁻¹ ∈ D.rel.base ∧ 0 < mu ∧
                ∀ (W : Set
                    (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
                  (v : List
                    (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
                  v ∈ W → RelWord.IsLemma49Input D.rel W eps mu rho →
                    Nonempty (HullFillingQuotient A N S
                      (GGT.RelLetter.listVal v) R)

/-- **The canonical quotient at every ambient group, from Lemma 4.4 and Lemma
4.9**: `torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49`, with
the filling alphabet taken from clause (d) over a quotient that may have
torsion. -/
theorem hullCanonicalQuotientStatementGeneral_of_lemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : HullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    HullCanonicalQuotientStatementGeneral.{u} := by
  intro G _ A N hN k S hS t R
  obtain ⟨D₀⟩ := hselect A S hN hS
  obtain ⟨D, ht, hacy⟩ := D₀.exists_acylindricalAdjoinPair t
  obtain ⟨eps44, rho44, mu44, hmu44, hgood44⟩ := h44 D R
  obtain ⟨eps49, rho49, mu49, hmu49, hgood49⟩ :=
    h49 D.rel D.embedded hacy
  refine ⟨D, max eps44 eps49, max rho44 rho49, min mu44 mu49,
    ht, lt_min hmu44 hmu49, ?_⟩
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
  obtain ⟨F⟩ := nonempty_fillingAlphabetData_of_peripheralPreservation_general D P
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

/-! ## One target -/

/-- **Hull's Theorem 7.1 for a single target, at every ambient group.**
`HullOneStepStatement` without the torsion-freeness binder. -/
def HullOneStepStatementGeneral : Prop :=
  ∀ {G : Type u} [Group G],
    ∀ (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N → ∀ {k : ℕ} {S : Fin k → Subgroup G},
      (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ (t : G) (R : ℕ),
        Nonempty (HullTower A N S (fun _ : Fin 1 => t) R)

open AuxiliaryPeripheralFamily in
/-- **The one-target theorem from the canonical quotient**, with Hull's §6
relator adjoining the target: `AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient`
at every ambient group. -/
theorem hullOneStepStatementGeneral_of_canonicalQuotient
    (hquot : HullCanonicalQuotientStatementGeneral.{u}) :
    HullOneStepStatementGeneral.{u} := by
  intro G _ A N hN k S hS t R
  obtain ⟨D, eps, rho, mu, ht, hmu, hgood⟩ :=
    hquot A N hN S hS t R
  obtain ⟨u, hu, v, hval, hsc, -⟩ :=
    exists_auxiliaryRelatorOfBaseLetterPublished_exact D hN t ht
      eps rho mu hmu
  obtain ⟨Q⟩ := hgood (RelWord.symmetrized v) v
    (RelWord.self_mem_symmetrized v) hsc
  have hrel : Q.q (t⁻¹ * u) = 1 := by
    rw [← hval, ← MonoidHom.mem_ker, Q.ker_eq]
    exact Subgroup.subset_normalClosure rfl
  have hqt : Q.q t = Q.q u := by
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel
  refine ⟨{ step := Q.toHullStep
            mem_map := ?_
            kerNormallyGenerated := ⟨{t⁻¹ * u}, by simp, ?_⟩ }⟩
  · intro _
    show Q.q t ∈ N.map Q.q
    rw [hqt]
    exact Subgroup.mem_map_of_mem _ hu
  · show Q.q.ker =
      Subgroup.normalClosure ((({t⁻¹ * u} : Finset G)) : Set G)
    rw [Q.ker_eq, hval, Finset.coe_singleton]

/-! ## The induction on targets -/

/-- **Hull's Theorem 7.1 for every number of targets, at every ambient group.** -/
def HullTowerStatementGeneral : Prop :=
  ∀ {G : Type u} [Group G],
    ∀ (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N → ∀ {k : ℕ} {S : Fin k → Subgroup G},
      (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ {m : ℕ} (t : Fin m → G)
        (R : ℕ), Nonempty (HullTower A N S t R)

/-- **The induction on `m`, at every ambient group.**  This is
`hullTower_of_oneStep`, where torsion-freeness of each intermediate quotient was
transported only to feed the next one-target step.  What the next step needs is
clause (d) (`suitable_map`), and that holds in any quotient. -/
theorem hullTowerGeneral_of_oneStep (h : HullOneStepStatementGeneral.{u}) :
    ∀ (m : ℕ) {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
        Suitable A.alphabet N → ∀ {k : ℕ}
        {S : Fin k → Subgroup G}, (∀ j : Fin k, Suitable A.alphabet (S j)) →
          ∀ (t : Fin m → G) (R : ℕ), Nonempty (HullTower A N S t R) := by
  intro m
  induction m with
  | zero =>
      intro G _ A N hN k S hS t R
      have hbot : Subgroup.normalClosure ((∅ : Finset G) : Set G) = ⊥ := by
        rw [Finset.coe_empty]
        exact le_antisymm
          (Subgroup.normalClosure_le_normal (Set.empty_subset _)) bot_le
      have hker : (MonoidHom.id G).ker = ⊥ := by
        ext x
        simp
      refine ⟨{
        step :=
          { Q := G
            group := inferInstance
            q := MonoidHom.id G
            surjective := fun y => ⟨y, rfl⟩
            hullSet := A
            alphabet_image := fun a ha => ha
            injOn := fun x _ y _ hxy => hxy
            suitable_map := by rw [Subgroup.map_id]; exact hN
            suitable_map_family := by
              intro j
              rw [Subgroup.map_id]
              exact hS j
            finiteOrder_lift := fun y _ => ⟨y, rfl, rfl⟩ }
        mem_map := fun i => Fin.elim0 i
        kerNormallyGenerated := by
          refine ⟨∅, by simp, ?_⟩
          show (MonoidHom.id G).ker
            = Subgroup.normalClosure ((∅ : Finset G) : Set G)
          rw [hker, hbot] }⟩
  | succ m ih =>
      intro G _ A N hN k S hS t R
      classical
      obtain ⟨s₁⟩ := h A hN hS (t 0) R
      obtain ⟨s₂⟩ := ih (N := N.map s₁.step.q)
        (S := fun j => (S j).map s₁.step.q) s₁.step.hullSet
        s₁.step.suitable_map s₁.step.suitable_map_family
        (fun i : Fin m => s₁.step.q (t i.succ)) R
      have hmapmap : (N.map s₁.step.q).map s₂.step.q
          = N.map (s₂.step.q.comp s₁.step.q) := by
        rw [Subgroup.map_map]
      have hmem : ∀ i : Fin (m + 1),
          (s₂.step.q.comp s₁.step.q) (t i) ∈ N.map (s₂.step.q.comp s₁.step.q) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · have h0 : s₂.step.q (s₁.step.q (t 0))
              ∈ (N.map s₁.step.q).map s₂.step.q :=
            Subgroup.mem_map_of_mem _ (s₁.mem_map 0)
          rw [hmapmap] at h0
          exact h0
        · intro j
          have hj := s₂.mem_map j
          rw [hmapmap] at hj
          exact hj
      have hkercomp : ∃ T : Finset G, T.card ≤ m + 1 ∧
          (s₂.step.q.comp s₁.step.q).ker = Subgroup.normalClosure (T : Set G) := by
        obtain ⟨T₁, hT₁card, hT₁ker⟩ := s₁.kerNormallyGenerated
        obtain ⟨T₂, hT₂card, hT₂ker⟩ := s₂.kerNormallyGenerated
        obtain ⟨σ, hσ⟩ : ∃ σ : s₁.step.Q → G, ∀ v, s₁.step.q (σ v) = v := by
          choose σ hσ using s₁.step.surjective
          exact ⟨σ, hσ⟩
        refine ⟨T₁ ∪ T₂.image σ, ?_, ?_⟩
        · refine le_trans (Finset.card_union_le _ _) ?_
          have himg : (T₂.image σ).card ≤ m :=
            le_trans Finset.card_image_le hT₂card
          omega
        · refine ker_comp_eq s₁.step.q s₁.step.surjective s₂.step.q
            (T₁ : Set G) (T₂ : Set s₁.step.Q) ((T₁ ∪ T₂.image σ : Finset G) : Set G)
            hT₁ker hT₂ker ?_ ?_ ?_
          · intro x hx
            exact Finset.mem_coe.mpr
              (Finset.mem_union_left _ (Finset.mem_coe.mp hx))
          · intro v hv
            refine ⟨σ v, ?_, hσ v⟩
            exact Finset.mem_coe.mpr (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hv)))
          · intro y hy
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hy) with hy₁ | hy₂
            · have hy1 : s₁.step.q y = 1 := by
                rw [← MonoidHom.mem_ker, hT₁ker]
                exact Subgroup.subset_normalClosure (Finset.mem_coe.mpr hy₁)
              rw [hy1, map_one]
            · obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy₂
              have hqy : s₁.step.q y = v := by rw [← hvy]; exact hσ v
              rw [hqy, ← MonoidHom.mem_ker, hT₂ker]
              exact Subgroup.subset_normalClosure (Finset.mem_coe.mpr hv)
      exact ⟨{ step := s₁.step.comp s₂.step
               mem_map := hmem
               kerNormallyGenerated := hkercomp }⟩

/-- **Hull's Theorem 7.1 for every `m`, from the one-relator case, at every
ambient group.** -/
theorem hullTowerStatementGeneral_of_oneStep (h : HullOneStepStatementGeneral.{u}) :
    HullTowerStatementGeneral.{u} := by
  intro G _ A N hN k S hS m t R
  exact hullTowerGeneral_of_oneStep h m A hN hS t R

/-! ## The published ball form -/

/-- **Hull's Theorem 7.1 in its published injectivity-radius form, with the kernel
datum, at every acylindrically hyperbolic group.**
`HullCorrectedInputs.HullBallFormStatementNG` without the torsion-freeness
binder. -/
def HullBallFormStatementGeneral : Prop :=
  ∀ {G : Type u} [Group G] [IsAcylindricallyHyperbolic G]
    (A : HullGeneratingSet G) {N : Subgroup G},
      Suitable A.alphabet N →
      ∀ {m : ℕ} (t : Fin m → G) (R : ℕ),
        Nonempty (Manuscript.NonMF.HullCorrectedInputs.HullQuotientNG N t
          (cayleyBall A.alphabet R))

/-- **The published ball form from the tower**, at every ambient group:
`hullBallFormNG_of_tower` with no torsion hypothesis. -/
theorem hullBallFormStatementGeneral_of_tower (h : HullTowerStatementGeneral.{u}) :
    HullBallFormStatementGeneral.{u} := by
  intro G _ _ A N hN m t R
  obtain ⟨D⟩ := h (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) A hN
    (fun j : Fin 0 => Fin.elim0 j) t R
  obtain ⟨T, hTcard, hTker⟩ := D.kerNormallyGenerated
  exact ⟨{ quotient :=
             { Q := D.step.Q
               group := D.step.group
               q := D.step.q
               surjective := D.step.surjective
               acylindricallyHyperbolic :=
                 isAcylindricallyHyperbolic_of_hullGeneratingSet D.step.hullSet
               injOn := D.step.injOn
               mem_map := D.mem_map
               finiteOrder_lift := D.step.finiteOrder_lift }
           kerNormallyGenerated := ⟨T, hTcard, hTker⟩ }⟩

/-- **The published ball form at every acylindrically hyperbolic group, from
Lemma 4.4, Lemma 4.9 and the simultaneous peripheral selection.** -/
theorem hullBallFormStatementGeneral_of_lemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : HullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    HullBallFormStatementGeneral.{u} :=
  hullBallFormStatementGeneral_of_tower
    (hullTowerStatementGeneral_of_oneStep
      (hullOneStepStatementGeneral_of_canonicalQuotient
        (hullCanonicalQuotientStatementGeneral_of_lemma44_of_lemma49 hselect h44 h49)))

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.hullCanonicalQuotientStatementGeneral_of_lemma44_of_lemma49
#audit_axioms GroupApproximation.HullSC.hullOneStepStatementGeneral_of_canonicalQuotient
#audit_axioms GroupApproximation.HullSC.hullTowerGeneral_of_oneStep
#audit_axioms GroupApproximation.HullSC.hullTowerStatementGeneral_of_oneStep
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_tower
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_lemma44_of_lemma49
