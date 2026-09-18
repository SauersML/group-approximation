import GroupApproximation.Steinberg.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# A finite presentation candidate for `St_I(ℤ)` (bh-met-91f)

For a finite index type `I`, the group `czSLFourFP_IntGroup I` has one generator `yᵢⱼ` for each
off-diagonal pair `(i, j)` and the relators

* `⁅yᵢⱼ, yₖₗ⁆ = 1` when `j ≠ k` and `l ≠ i`;
* `⁅yᵢⱼ, yⱼₖ⁆ = yᵢₖ` when `i, j, k` are distinct.

There are finitely many generators and relators, so the group is finitely presented
(`czSLFourFP_intGroup_isFinitelyPresented`).  The map `yᵢⱼ ↦ xᵢⱼ(1)` is a homomorphism to
`St_I(ℤ)` (`czSLFourFP_phi`); its inverse is built in `ElemFPCharZeroSLFourFPIntIso`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

noncomputable section

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- Off-diagonal index pairs: the generators of the presentation. -/
abbrev czSLFourFP_Root := {p : I × I // p.1 ≠ p.2}

/-- Index data of the commutation relators. -/
abbrev czSLFourFP_CommDom :=
  {q : czSLFourFP_Root I × czSLFourFP_Root I // q.1.1.2 ≠ q.2.1.1 ∧ q.2.1.2 ≠ q.1.1.1}

/-- Index data of the adjacent relators. -/
abbrev czSLFourFP_AdjDom := {q : I × I × I // q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2 ∧ q.1 ≠ q.2.2}

/-- Commutation relators `⁅yᵢⱼ, yₖₗ⁆`. -/
def czSLFourFP_commRel (q : czSLFourFP_CommDom I) : FreeGroup (czSLFourFP_Root I) :=
  ⁅FreeGroup.of q.1.1, FreeGroup.of q.1.2⁆

/-- Adjacent relators `⁅yᵢⱼ, yⱼₖ⁆ yᵢₖ⁻¹`. -/
def czSLFourFP_adjRel (q : czSLFourFP_AdjDom I) : FreeGroup (czSLFourFP_Root I) :=
  ⁅FreeGroup.of (⟨(q.1.1, q.1.2.1), q.2.1⟩ : czSLFourFP_Root I),
      FreeGroup.of (⟨(q.1.2.1, q.1.2.2), q.2.2.1⟩ : czSLFourFP_Root I)⁆ *
    (FreeGroup.of (⟨(q.1.1, q.1.2.2), q.2.2.2⟩ : czSLFourFP_Root I))⁻¹

/-- The relator set. -/
def czSLFourFP_intRels : Set (FreeGroup (czSLFourFP_Root I)) :=
  Set.range (czSLFourFP_commRel I) ∪ Set.range (czSLFourFP_adjRel I)

instance czSLFourFP_intRels_finite : Finite ↥(czSLFourFP_intRels I) :=
  ((Set.finite_range (czSLFourFP_commRel I)).union
    (Set.finite_range (czSLFourFP_adjRel I))).to_subtype

/-- The presented group. -/
abbrev czSLFourFP_IntGroup := PresentedGroup (czSLFourFP_intRels I)

/-- The presented group is finitely presented. -/
theorem czSLFourFP_intGroup_isFinitelyPresented :
    Group.IsFinitelyPresented (czSLFourFP_IntGroup I) :=
  inferInstance

/-- The generator `yᵢⱼ`. -/
def czSLFourFP_y (i j : I) (hij : i ≠ j) : czSLFourFP_IntGroup I :=
  PresentedGroup.of (⟨(i, j), hij⟩ : czSLFourFP_Root I)

/-- Commutation relation in the presented group. -/
theorem czSLFourFP_y_commute (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) : Commute (czSLFourFP_y I i j hij) (czSLFourFP_y I k l hkl) := by
  have hmem : czSLFourFP_commRel I ⟨(⟨(i, j), hij⟩, ⟨(k, l), hkl⟩), hjk, hli⟩ ∈
      czSLFourFP_intRels I :=
    Set.mem_union_left _ (Set.mem_range_self _)
  have h1 := PresentedGroup.one_of_mem hmem
  rw [czSLFourFP_commRel, map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_commute.mp h1

/-- Adjacent relation in the presented group. -/
theorem czSLFourFP_y_commutator (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅czSLFourFP_y I i j hij, czSLFourFP_y I j k hjk⁆ = czSLFourFP_y I i k hik := by
  have hmem : czSLFourFP_adjRel I ⟨(i, j, k), hij, hjk, hik⟩ ∈ czSLFourFP_intRels I :=
    Set.mem_union_right _ (Set.mem_range_self _)
  have h1 := PresentedGroup.one_of_mem hmem
  rw [czSLFourFP_adjRel, map_mul, map_inv, map_commutatorElement] at h1
  exact mul_inv_eq_one.mp h1

/-- Images `xᵢⱼ(1)` of the generators. -/
def czSLFourFP_phiGen (p : czSLFourFP_Root I) : SteinbergGroup I ℤ :=
  SteinbergGroup.x p.1.1 p.1.2 p.2 1

theorem czSLFourFP_phi_rels : ∀ r ∈ czSLFourFP_intRels I,
    FreeGroup.lift (czSLFourFP_phiGen I) r = 1 := by
  rintro r (⟨⟨⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, l⟩, hkl⟩⟩, hjk, hli⟩, rfl⟩ |
    ⟨⟨⟨i, j, k⟩, hij, hjk, hik⟩, rfl⟩)
  · simp only [czSLFourFP_commRel, map_commutatorElement, FreeGroup.lift_apply_of]
    exact (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk hli (1 : ℤ) 1).commutator_eq
  · simp only [czSLFourFP_adjRel, map_mul, map_inv, map_commutatorElement,
      FreeGroup.lift_apply_of]
    change ⁅SteinbergGroup.x i j hij (1 : ℤ), SteinbergGroup.x j k hjk 1⁆ *
      (SteinbergGroup.x i k hik 1)⁻¹ = 1
    rw [SteinbergGroup.x_commutator i j k hij hjk hik, one_mul, mul_inv_cancel]

/-- The homomorphism `φ : yᵢⱼ ↦ xᵢⱼ(1)`. -/
def czSLFourFP_phi : czSLFourFP_IntGroup I →* SteinbergGroup I ℤ :=
  PresentedGroup.toGroup (czSLFourFP_phi_rels I)

theorem czSLFourFP_phi_y (i j : I) (hij : i ≠ j) :
    czSLFourFP_phi I (czSLFourFP_y I i j hij) = SteinbergGroup.x i j hij 1 :=
  PresentedGroup.toGroup.of (czSLFourFP_phi_rels I)

end

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_Root
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_CommDom
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_AdjDom
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_commRel
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_adjRel
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_intRels
#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_intRels_finite
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_IntGroup
#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_intGroup_isFinitelyPresented
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_y
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_y_commute
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_y_commutator
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_phiGen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_phi_rels
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_phi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_phi_y

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
