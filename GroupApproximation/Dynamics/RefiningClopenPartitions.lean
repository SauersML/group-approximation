import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Real
import GroupApproximation.Meta.AxiomGuard

/-!
# Refining clopen partitions with mesh tending to zero

`non_mf_groups_exist.tex`, lines 1428–1429 (proof of `lem:chain-core-models`, general `X`):
"For general $X$, choose refining finite clopen partitions $\mathcal P_m$ with mesh tending to
zero."  Lines 1443–1444: "every locally constant function is constant on a sufficiently fine
partition."

A finite clopen partition of `X` is a `DiscreteQuotient X`; its atoms are the fibres of `proj`,
and there are finitely many of them when `X` is compact (Mathlib's instance on
`DiscreteQuotient`).  `S ≤ S'` means that `S` refines `S'`.

* `IsRefiningClopenPartitions S`: `S` is antitone and the atoms of `S m` have diameters tending
  to zero.
* `exists_discreteQuotient_mesh_lt`, `exists_refiningClopenPartitions`: on a compact, totally
  disconnected metric space such sequences exist.
* `exists_forall_proj_eq_imp_of_locallyConstant`: a locally constant function is constant on
  the atoms of every sufficiently fine `S m`.
-/

namespace GroupApproximation
namespace ChainCore

variable {X : Type*}

/-- Refining finite clopen partitions with mesh tending to zero. -/
structure IsRefiningClopenPartitions [MetricSpace X] (S : ℕ → DiscreteQuotient X) : Prop where
  antitone : Antitone S
  mesh_lt : ∀ ε > 0, ∃ m, ∀ x y, (S m).proj x = (S m).proj y → dist x y < ε

/-- Points in the same atom of a finer partition lie in the same atom of a coarser one. -/
theorem proj_eq_of_le [TopologicalSpace X] {A B : DiscreteQuotient X} (h : A ≤ B) {x y : X}
    (hxy : A.proj x = A.proj y) : B.proj x = B.proj y :=
  (DiscreteQuotient.ofLE_proj h x).symm.trans
    ((congrArg (DiscreteQuotient.ofLE h) hxy).trans (DiscreteQuotient.ofLE_proj h y))

/-- A compact, totally disconnected metric space has finite clopen partitions of arbitrarily
small mesh. -/
theorem exists_discreteQuotient_mesh_lt [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : DiscreteQuotient X, ∀ x y, Q.proj x = Q.proj y → dist x y < ε := by
  have hKc : IsCompact {p : X × X | ε ≤ dist p.1 p.2} :=
    (isClosed_le continuous_const continuous_dist).isCompact
  have hcover : {p : X × X | ε ≤ dist p.1 p.2} ⊆
      ⋃ Q : DiscreteQuotient X, {p : X × X | Q.proj p.1 ≠ Q.proj p.2} := by
    rintro ⟨x, y⟩ hxy
    have hxy' : ε ≤ dist x y := hxy
    have hne : x ≠ y := by
      rintro rfl
      rw [dist_self] at hxy'
      exact not_le.2 hε hxy'
    obtain ⟨Q, hQ⟩ : ∃ Q : DiscreteQuotient X, Q.proj x ≠ Q.proj y := by
      by_contra h
      exact hne (DiscreteQuotient.eq_of_forall_proj_eq fun Q ↦ by
        by_contra hQ
        exact h ⟨Q, hQ⟩)
    exact Set.mem_iUnion.2 ⟨Q, hQ⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun Q : DiscreteQuotient X ↦ {p : X × X | Q.proj p.1 ≠ Q.proj p.2})
    (fun Q ↦ isOpen_ne_fun (Q.proj_continuous.comp continuous_fst)
      (Q.proj_continuous.comp continuous_snd)) hcover
  refine ⟨t.inf id, fun x y hxy ↦ ?_⟩
  by_contra hlt
  have hp : (x, y) ∈ {p : X × X | ε ≤ dist p.1 p.2} := not_lt.1 hlt
  obtain ⟨Q, hQt, hQ⟩ := Set.mem_iUnion₂.1 (ht hp)
  have hle : t.inf id ≤ Q := Finset.inf_le hQt
  have hQ' : Q.proj x ≠ Q.proj y := hQ
  exact hQ' (proj_eq_of_le hle hxy)

/-- **Refining finite clopen partitions with mesh tending to zero** exist on a compact, totally
disconnected metric space: "For general $X$, choose refining finite clopen partitions
$\mathcal P_m$ with mesh tending to zero" (`non_mf_groups_exist.tex`, lines 1428–1429). -/
theorem exists_refiningClopenPartitions [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] : ∃ S : ℕ → DiscreteQuotient X, IsRefiningClopenPartitions S := by
  choose Q hQ using fun n : ℕ ↦
    exists_discreteQuotient_mesh_lt (X := X) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  refine ⟨fun m ↦ (Finset.range (m + 1)).inf Q, ⟨fun m l hml ↦ ?_, fun ε hε ↦ ?_⟩⟩
  · exact Finset.inf_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hml))
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, fun x y hxy ↦ (hQ n x y (proj_eq_of_le ?_ hxy)).trans hn⟩
    exact Finset.inf_le (Finset.self_mem_range_succ n)

/-- **Every locally constant function is constant on a sufficiently fine partition**
(`non_mf_groups_exist.tex`, lines 1443–1444). -/
theorem exists_forall_proj_eq_imp_of_locallyConstant [MetricSpace X] [CompactSpace X]
    {S : ℕ → DiscreteQuotient X} (hS : IsRefiningClopenPartitions S) {Y : Type*}
    (f : LocallyConstant X Y) :
    ∃ m, ∀ l, m ≤ l → ∀ x y, (S l).proj x = (S l).proj y → f x = f y := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set X))
    (c := fun i : Y ↦ {x : X | f x = i}) isCompact_univ
    (fun i ↦ f.isLocallyConstant.isOpen_fiber i) fun x _ ↦ Set.mem_iUnion.2 ⟨f x, rfl⟩
  obtain ⟨m, hm⟩ := hS.mesh_lt δ hδ
  refine ⟨m, fun l hml x y hxy ↦ ?_⟩
  have hxy' : dist x y < δ := hm x y (proj_eq_of_le (hS.antitone hml) hxy)
  obtain ⟨i, hi⟩ := hball x (Set.mem_univ x)
  have hx : f x = i := hi (Metric.mem_ball_self hδ)
  have hy' : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    exact hxy'
  have hy : f y = i := hi hy'
  exact hx.trans hy.symm

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.proj_eq_of_le
#audit_axioms GroupApproximation.ChainCore.exists_discreteQuotient_mesh_lt
#audit_axioms GroupApproximation.ChainCore.exists_refiningClopenPartitions
#audit_axioms GroupApproximation.ChainCore.exists_forall_proj_eq_imp_of_locallyConstant
