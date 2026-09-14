import GroupApproximation.Algebra.StepanovNormalStructure
import GroupApproximation.Dynamics.ClopenCrossedProductPairDependence
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalDenseOrbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity of `G_X` along the Stepanov route

`simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, tex l.81–85 (census `9424f59fd820`):

> Simplicity of $G_X$ also follows from Stepanov's theorem on the normal structure of $\GL_n$
> [Stepanov, Theorem 4.4], since the ring is simple [ClarkEdie, Corollary 4.6] and any two of its
> elements $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$, by a dimension count on a tower over one
> small cylinder.

The sentence at the note's generality, an infinite minimal subshift `X` over a finite alphabet
and `R = LC(X, F₂) ⋊_T ℤ`, with every cited step proved:

* "the ring is simple": `SimpleKazhdanSofic.isSimpleRing`, over minimality
  (`minimalSubshift_dense_orbits`) and the absence of periodic points (`zpow_apply_ne_self`);
* "any two of its elements p, q satisfy pr + qs = 0 with (r, s) ≠ 0, by a dimension count on a
  tower over one small cylinder": `exists_pair_dependence` (`PrintedSubshiftRingPairDependence`);
* the hypothesis of Stepanov's Theorem 4.4 at the ideal `0`: `stepanovConditionB_of_pairDependence`,
  with `b = 1` and `α = e_i r + e_j s`, `α_l = 0` and `(aα)_l = a_{li} r + a_{lj} s = 0`;
* Theorem 4.4 over a simple ring: `StepanovNormalStructure.sandwich_of_conditionB`;
* "Simplicity of G_X also follows": `isSimpleGroup_elementaryGroup_stepanov`, through the sandwich,
  `Z(R) = F₂` (`mem_center_iff_eq_zero_or_one`) and `EL_n(R) ≠ 1`, for every `n ≥ 3`
  (`PrintedStepanovRouteSimplicity`).  It also discharges `PrintedSimplicityStatement` of
  `MainAssembly` by this route (`printedSimplicityStatement_stepanov`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift

/-- **Pair dependence gives Stepanov's condition (b) at the ideal `0`**, with `b = 1` and
`α = e_i r + e_j s` for `p = a_{li}`, `q = a_{lj}`, `l ∉ {i, j}`. -/
theorem stepanovConditionB_of_pairDependence {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (hcard : 3 ≤ Fintype.card ι)
    (hpair : ∀ p q : R, ∃ r s : R, (r, s) ≠ 0 ∧ p * r + q * s = 0) :
    StepanovNormalStructure.StepanovConditionB ι R := by
  intro a
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  obtain ⟨l, hli, hlj⟩ := exists_third_index hcard i j
  obtain ⟨r, s, hrs, hsum⟩ := hpair ((a : Matrix ι ι R) l i) ((a : Matrix ι ι R) l j)
  refine ⟨1, Subgroup.one_mem _, Pi.single i r + Pi.single j s, fun h => hrs ?_, l, l, ?_, ?_⟩
  · have hi := congrFun h i
    have hj := congrFun h j
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero] at hi
    rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add] at hj
    exact Prod.mk_eq_zero.mpr ⟨hi, hj⟩
  · rw [Pi.add_apply, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, add_zero]
  · rw [inv_one, one_mul, mul_one, Matrix.mulVec_add, Matrix.mulVec_single, Matrix.mulVec_single,
      Pi.add_apply]
    exact hsum

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]

omit [DiscreteTopology A] [Finite A] in
/-- **"any two of its elements $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$"**, for the ring of
`thm:main`, by the dimension count on a tower over one cylinder. -/
theorem pairDependence_R (S : Subshift A ℤ) (hinf : Infinite S.carrier) (p q : R S) :
    ∃ r s : R S, (r, s) ≠ 0 ∧ p * r + q * s = 0 := by
  haveI : Nonempty S.carrier := hinf.nonempty
  exact exists_pair_dependence (subshiftHomeo S) (ZMod 2) p q

omit [DiscreteTopology A] [Finite A] in
theorem isMinimalSystem_subshiftHomeo (S : Subshift A ℤ) (hmin : IsMinimal S) :
    IsMinimalSystem (subshiftHomeo S) :=
  minimalSubshift_dense_orbits S hmin

omit [Finite A] in
theorem subshiftHomeo_zpow_ne_self (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) : ∀ j : ℤ, j ≠ 0 → ∀ y : S.carrier, (subshiftHomeo S ^ j) y ≠ y := by
  haveI := hinf
  exact fun j hj y => zpow_apply_ne_self (subshiftHomeo S) (isMinimalSystem_subshiftHomeo S hmin) hj y

/-- **"the ring is simple"**, for an infinite minimal subshift. -/
theorem isSimpleRing_R (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    IsSimpleRing (R S) := by
  haveI := compactSpace_carrier S
  haveI : Nonempty S.carrier := hinf.nonempty
  exact isSimpleRing (subshiftHomeo S) (isMinimalSystem_subshiftHomeo S hmin)
    (subshiftHomeo_zpow_ne_self S hinf hmin) (ZMod 2)

/-- **Simplicity of `G_X` along the Stepanov route**, for every `n ≥ 3`. -/
theorem isSimpleGroup_elementaryGroup_stepanov (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup ↥(elementaryGroup (Fin n) (R S)) := by
  haveI := compactSpace_carrier S
  haveI : Nonempty S.carrier := hinf.nonempty
  haveI := isSimpleRing_R S hinf hmin
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  refine StepanovNormalStructure.isSimpleGroup_elementaryGroup_of_conditionB hcard
    (stepanovConditionB_of_pairDependence hcard (pairDependence_R S hinf)) fun u hu => ?_
  have hc : (u : R S) ∈ Set.center (R S) :=
    Semigroup.mem_center_iff.mpr fun x => (hu x).eq.symm
  rcases (mem_center_iff_eq_zero_or_one (subshiftHomeo S) (isMinimalSystem_subshiftHomeo S hmin)
      (subshiftHomeo_zpow_ne_self S hinf hmin) (u : R S)).mp hc with h0 | h1
  · exact absurd h0 u.ne_zero
  · exact h1

end Subshift

/-- **Printed** (tex l.83–85): "any two of its elements $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$,
by a dimension count on a tower over one small cylinder", for the ring of every infinite subshift. -/
def PrintedSubshiftRingPairDependence : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → ∀ p q : R S, ∃ r s : R S, (r, s) ≠ 0 ∧ p * r + q * s = 0

theorem printedSubshiftRingPairDependence : PrintedSubshiftRingPairDependence :=
  fun _ _ _ _ S hinf p q => pairDependence_R S hinf p q

/-- **Printed** (tex l.81–85): for an infinite minimal subshift, the ring is simple, it satisfies
the hypothesis of Stepanov's Theorem 4.4, and `EL_n(R)` is simple for every `n ≥ 3`. -/
def PrintedStepanovRouteSimplicity : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ∀ n : ℕ, 3 ≤ n →
      IsSimpleRing (R S) ∧ StepanovNormalStructure.StepanovConditionB (Fin n) (R S) ∧
        IsSimpleGroup ↥(elementaryGroup (Fin n) (R S))

theorem printedStepanovRouteSimplicity : PrintedStepanovRouteSimplicity := by
  intro A _ _ _ S hinf hmin n hn
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  exact ⟨isSimpleRing_R S hinf hmin,
    stepanovConditionB_of_pairDependence hcard (pairDependence_R S hinf),
    isSimpleGroup_elementaryGroup_stepanov S hinf hmin hn⟩

/-- `MainAssembly`'s simplicity piece, discharged along the Stepanov route. -/
theorem printedSimplicityStatement_stepanov : PrintedSimplicityStatement :=
  fun _ _ _ _ S hinf hmin _ hn => isSimpleGroup_elementaryGroup_stepanov S hinf hmin hn

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.stepanovConditionB_of_pairDependence
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isSimpleGroup_elementaryGroup_stepanov
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSubshiftRingPairDependence
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedStepanovRouteSimplicity
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSimplicityStatement_stepanov
