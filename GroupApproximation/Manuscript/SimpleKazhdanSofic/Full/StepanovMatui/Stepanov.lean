import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.NormalStructure
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.PairDependence
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalDenseOrbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity of `EL_n(LC(X, F₂) ⋊_T ℤ)` along the Stepanov route

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315:

> For the ring $\LC(X,\F_2)\rtimes_T\Z$ of Theorem~\ref{thm:main}, simplicity also follows from
> Stepanov's theorem on the normal structure of $\GL_n$ [Stepanov, Theorem 4.4]: this ring is
> simple [ClarkEdie, Corollary 4.6], and for any $p,q$ in it there are $r,r'$, not both $0$, with
> $pr+qr'=0$, by a dimension count on a tower over one small cylinder.

Every cited step is proved:

* "this ring is simple": `SimpleKazhdanSofic.isSimpleRing` (Clark–Edie Cor. 4.6 at this ring),
  over minimality (`minimalSubshift_dense_orbits`) and aperiodicity (`zpow_apply_ne_self`);
* "for any p, q there are r, r', not both 0, with pr + qr' = 0": `exists_pair_dependence`
  (`PairDependence`), `PrintedSubshiftRingPairDependence`;
* the hypothesis of Stepanov's Theorem 4.4 at the ideal `0`: `stepanovConditionB_of_pairDependence`
  (`b = 1`, `α = e_i r + e_j s`, `α_l = 0`, `(aα)_l = a_{li} r + a_{lj} s = 0`);
* Theorem 4.4 over a simple ring: `sandwich_of_conditionB` (`NormalStructure`);
* "simplicity also follows": `isSimpleGroup_elementaryGroup_stepanov` (the ring of `thm:main`,
  every `n ≥ 3`), and `isSimpleGroup_elementaryGroup_stepanov_of_minimal` (every minimal
  homeomorphism of an infinite compact Hausdorff totally separated space).

Adapted from the foreign never-wired `Manuscript/SimpleKazhdanSofic/StepanovSimplicity.lean`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui

open SymbolicDynamics.FullShift

/-- **Pair dependence gives Stepanov's condition (b) at the ideal `0`**, with `b = 1` and
`α = e_i r + e_j s` for `p = a_{li}`, `q = a_{lj}`, `l ∉ {i, j}` (tex l.307–315). -/
theorem stepanovConditionB_of_pairDependence {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (hcard : 3 ≤ Fintype.card ι)
    (hpair : ∀ p q : R, ∃ r s : R, (r, s) ≠ 0 ∧ p * r + q * s = 0) :
    StepanovConditionB ι R := by
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

/-- **The Stepanov route at a minimal homeomorphism**: for a minimal homeomorphism `T` of an
infinite compact Hausdorff totally separated space, `EL_n(LC(Y, F₂) ⋊_T ℤ)` is simple, `n ≥ 3`. -/
theorem isSimpleGroup_elementaryGroup_stepanov_of_minimal {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] [TotallySeparatedSpace Y] [Infinite Y] (T : Y ≃ₜ Y)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) := by
  have hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : Y, (T ^ j) y ≠ y :=
    fun j hj y => SimpleKazhdanSofic.zpow_apply_ne_self T hmin hj y
  haveI := SimpleKazhdanSofic.isSimpleRing T hmin hfree (ZMod 2)
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  refine isSimpleGroup_elementaryGroup_of_conditionB hcard
    (stepanovConditionB_of_pairDependence hcard (exists_pair_dependence T (ZMod 2))) fun u hu => ?_
  have hc : (u : ClopenCrossedProduct T (ZMod 2)) ∈ Set.center (ClopenCrossedProduct T (ZMod 2)) :=
    Semigroup.mem_center_iff.mpr fun x => (hu x).eq.symm
  rcases (SimpleKazhdanSofic.mem_center_iff_eq_zero_or_one T hmin hfree
      (u : ClopenCrossedProduct T (ZMod 2))).mp hc with h0 | h1
  · exact absurd h0 u.ne_zero
  · exact h1

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]

omit [DiscreteTopology A] [Finite A] in
/-- **"for any $p,q$ in it there are $r,r'$, not both $0$, with $pr+qr'=0$"** (tex l.312–315), for
the ring of `thm:main`, by the dimension count on a tower over one cylinder. -/
theorem pairDependence_R (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (p q : SimpleKazhdanSofic.R S) :
    ∃ r s : SimpleKazhdanSofic.R S, (r, s) ≠ 0 ∧ p * r + q * s = 0 := by
  haveI := hinf
  exact exists_pair_dependence (SimpleKazhdanSofic.subshiftHomeo S) (ZMod 2) p q

omit [DiscreteTopology A] [Finite A] in
theorem isMinimalSystem_subshiftHomeo (S : Subshift A ℤ) (hmin : SimpleKazhdanSofic.IsMinimal S) :
    SimpleKazhdanSofic.IsMinimalSystem (SimpleKazhdanSofic.subshiftHomeo S) :=
  SimpleKazhdanSofic.minimalSubshift_dense_orbits S hmin

omit [Finite A] in
theorem subshiftHomeo_zpow_ne_self (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) :
    ∀ j : ℤ, j ≠ 0 → ∀ y : S.carrier, (SimpleKazhdanSofic.subshiftHomeo S ^ j) y ≠ y := by
  haveI := hinf
  exact fun j hj y => SimpleKazhdanSofic.zpow_apply_ne_self (SimpleKazhdanSofic.subshiftHomeo S)
    (isMinimalSystem_subshiftHomeo S hmin) hj y

/-- **"this ring is simple"** (tex l.312), for an infinite minimal subshift. -/
theorem isSimpleRing_R (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) : IsSimpleRing (SimpleKazhdanSofic.R S) := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  haveI := hinf
  exact SimpleKazhdanSofic.isSimpleRing (SimpleKazhdanSofic.subshiftHomeo S)
    (isMinimalSystem_subshiftHomeo S hmin) (subshiftHomeo_zpow_ne_self S hinf hmin) (ZMod 2)

/-- **"simplicity also follows from Stepanov's theorem"** (tex l.309–312): `EL_n(R)` is simple for
the ring `R` of `thm:main` and every `n ≥ 3`. -/
theorem isSimpleGroup_elementaryGroup_stepanov (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (SimpleKazhdanSofic.R S)) := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  haveI := hinf
  haveI := isSimpleRing_R S hinf hmin
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  refine isSimpleGroup_elementaryGroup_of_conditionB hcard
    (stepanovConditionB_of_pairDependence hcard (pairDependence_R S hinf)) fun u hu => ?_
  have hc : (u : SimpleKazhdanSofic.R S) ∈ Set.center (SimpleKazhdanSofic.R S) :=
    Semigroup.mem_center_iff.mpr fun x => (hu x).eq.symm
  rcases (SimpleKazhdanSofic.mem_center_iff_eq_zero_or_one (SimpleKazhdanSofic.subshiftHomeo S)
      (isMinimalSystem_subshiftHomeo S hmin) (subshiftHomeo_zpow_ne_self S hinf hmin)
      (u : SimpleKazhdanSofic.R S)).mp hc with h0 | h1
  · exact absurd h0 u.ne_zero
  · exact h1

end Subshift

/-- **Printed** (tex l.312–315): "for any $p,q$ in it there are $r,r'$, not both $0$, with
$pr+qr'=0$, by a dimension count on a tower over one small cylinder", for every infinite
subshift. -/
def PrintedSubshiftRingPairDependence : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → ∀ p q : SimpleKazhdanSofic.R S,
      ∃ r s : SimpleKazhdanSofic.R S, (r, s) ≠ 0 ∧ p * r + q * s = 0

theorem printedSubshiftRingPairDependence : PrintedSubshiftRingPairDependence :=
  fun _ _ _ _ S hinf p q => pairDependence_R S hinf p q

/-- **Printed** (tex l.309–315): for the ring of `thm:main`, the ring is simple, it satisfies the
hypothesis of Stepanov's Theorem 4.4, and `EL_n(R)` is simple for every `n ≥ 3`. -/
def PrintedStepanovRouteSimplicity : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → SimpleKazhdanSofic.IsMinimal S → ∀ n : ℕ, 3 ≤ n →
      IsSimpleRing (SimpleKazhdanSofic.R S) ∧ StepanovConditionB (Fin n) (SimpleKazhdanSofic.R S) ∧
        IsSimpleGroup ↥(elementaryGroup (Fin n) (SimpleKazhdanSofic.R S))

theorem printedStepanovRouteSimplicity : PrintedStepanovRouteSimplicity := by
  intro A _ _ _ S hinf hmin n hn
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  exact ⟨isSimpleRing_R S hinf hmin,
    stepanovConditionB_of_pairDependence hcard (pairDependence_R S hinf),
    isSimpleGroup_elementaryGroup_stepanov S hinf hmin hn⟩

/-- `MainAssembly`'s simplicity piece, discharged along the Stepanov route. -/
theorem printedSimplicityStatement_stepanov : SimpleKazhdanSofic.PrintedSimplicityStatement :=
  fun _ _ _ _ S hinf hmin _ hn => isSimpleGroup_elementaryGroup_stepanov S hinf hmin hn

end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.stepanovConditionB_of_pairDependence
#audit_axioms GroupApproximation.Full.StepanovMatui.isSimpleGroup_elementaryGroup_stepanov_of_minimal
#audit_axioms GroupApproximation.Full.StepanovMatui.isSimpleGroup_elementaryGroup_stepanov
#audit_closed_axioms GroupApproximation.Full.StepanovMatui.printedSubshiftRingPairDependence
#audit_closed_axioms GroupApproximation.Full.StepanovMatui.printedStepanovRouteSimplicity
#audit_closed_axioms GroupApproximation.Full.StepanovMatui.printedSimplicityStatement_stepanov
