import GroupApproximation.Analysis.GroupVonNeumannIIOneFactor
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Set.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Infinite simple groups have infinite conjugacy classes, and `L(G)` is a II₁ factor

`simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, "Brown's formulation", tex 278–283
(census 649cb1f80, row `6e8db7db6717` and the first clause of row `97438886a277`), for `G` as in
Theorem `thm:general`:

> Since `G` is infinite and simple, its nontrivial conjugacy classes are infinite and `G` is not
> residually finite.  So `L(G)` is a `II₁` factor, ...

* `isICC_of_isSimpleGroup_of_infinite`: the printed step "its nontrivial conjugacy classes are
  infinite".  If the class of `g ≠ 1` were finite, the centralizer `L = {h : h g h⁻¹ = g}` of `g`
  (the stabilizer of `g` under conjugation) would have finite index, since the index of a stabilizer
  is the size of the orbit.  So its normal core is a normal subgroup of finite index.  By simplicity
  the core is either `⊥`, and then `G` embeds in a finite quotient, or `⊤`, and then `g` is
  central.  In the second case the centre is a nontrivial normal subgroup, hence everything, so `G`
  is a commutative simple group, whose cardinality is prime, against `Infinite G`.
* `printedInfiniteSimpleICCNotResiduallyFinite`: the sentence at tex 278–280, stated for every
  infinite simple group, which covers the groups of `thm:general`.  "Not residually
  finite" is `NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`.
* `printedInfiniteSimpleGroupVonNeumannIIOneFactor`: "So `L(G)` is a II₁ factor", through
  `IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra` from the infinite conjugacy classes.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open TwoSidedRegularCommutant

universe u

variable (G : Type u) [Group G]

/-- **An infinite simple group has infinite conjugacy classes.** -/
theorem isICC_of_isSimpleGroup_of_infinite [IsSimpleGroup G] [Infinite G] : IsICC G := by
  intro g hg
  show ¬ Set.Finite {x : G | IsConj g x}
  intro hfin
  have horbit : MulAction.orbit (ConjAct G) g = {x : G | IsConj g x} := by
    ext x
    rw [Set.mem_setOf_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  -- the centralizer of `g`, as the stabilizer of `g` under conjugation
  let L : Subgroup G :=
    Subgroup.comap (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
      (MulAction.stabilizer (ConjAct G) g)
  have hLindex : L.index = (MulAction.stabilizer (ConjAct G) g).index :=
    Subgroup.index_comap_of_surjective _
      (fun y ↦ ⟨ConjAct.ofConjAct y, ConjAct.toConjAct_ofConjAct y⟩)
  have hindex : L.index ≠ 0 := by
    rw [hLindex, MulAction.index_stabilizer, horbit]
    exact Set.ncard_ne_zero_of_mem (show g ∈ {x : G | IsConj g x} from IsConj.refl g) hfin
  have hmemL : ∀ h ∈ L, h * g = g * h := by
    intro h hh
    have hs : ConjAct.toConjAct h • g = g :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hh)
    rw [ConjAct.toConjAct_smul] at hs
    calc h * g = h * g * h⁻¹ * h := by rw [inv_mul_cancel_right]
      _ = g * h := by rw [hs]
  haveI : L.FiniteIndex := Subgroup.finiteIndex_iff.mpr hindex
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore inferInstance with hbot | htop
  · haveI : Finite (G ⧸ L.normalCore) := L.normalCore.finite_quotient_of_finiteIndex
    have hinj : Function.Injective (QuotientGroup.mk' L.normalCore) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hbot
    haveI : Finite G := Finite.of_injective _ hinj
    exact not_finite G
  · have hcentral : ∀ h : G, h * g = g * h := by
      intro h
      have hmem : h ∈ L.normalCore := by
        rw [htop]
        exact Subgroup.mem_top h
      exact hmemL h (L.normalCore_le hmem)
    have hg_center : g ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hcentral
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with
      hcbot | hctop
    · rw [hcbot] at hg_center
      exact hg (Subgroup.mem_bot.mp hg_center)
    · have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        have hb : b ∈ Subgroup.center G := by
          rw [hctop]
          exact Subgroup.mem_top b
        exact Subgroup.mem_center_iff.mp hb a
      haveI : IsMulCommutative G := isMulCommutative_iff.mpr hcomm
      have hprime : (Nat.card G).Prime :=
        (Group.is_simple_iff_prime_card (α := G)).mp inferInstance
      rw [Nat.card_eq_zero_of_infinite] at hprime
      exact Nat.not_prime_zero hprime

/-- **tex 278–280** (census `6e8db7db6717`): "Since `G` is infinite and simple, its nontrivial
conjugacy classes are infinite and `G` is not residually finite." -/
def PrintedInfiniteSimpleICCNotResiduallyFinite : Prop :=
  ∀ (G : Type u) [Group G], IsSimpleGroup G → Infinite G →
    IsICC G ∧ ¬ IsResiduallyFinite G

theorem printedInfiniteSimpleICCNotResiduallyFinite :
    PrintedInfiniteSimpleICCNotResiduallyFinite.{u} := by
  intro G _ _ _
  exact ⟨isICC_of_isSimpleGroup_of_infinite G,
    NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite G⟩

/-- **tex 280**, first clause of census `97438886a277`: "So `L(G)` is a `II₁` factor", for the
infinite simple group `G`. -/
def PrintedInfiniteSimpleGroupVonNeumannIIOneFactor : Prop :=
  ∀ (G : Type u) [Group G], IsSimpleGroup G → Infinite G →
    IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra G)

theorem printedInfiniteSimpleGroupVonNeumannIIOneFactor :
    PrintedInfiniteSimpleGroupVonNeumannIIOneFactor.{u} := by
  intro G _ _ _
  exact IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra G
    (isICC_of_isSimpleGroup_of_infinite G)

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedInfiniteSimpleICCNotResiduallyFinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedInfiniteSimpleGroupVonNeumannIIOneFactor
