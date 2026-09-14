import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Dynamics.ReturnPlacement
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Separation.Profinite

/-!
# The ring and clopen partitions (simple_kazhdan_sofic_group.tex, tex 70–82)

`simple_kazhdan_sofic_group.tex` at bf961c128, "The ring and property (T)", tex 70–82:

> Write $e_U$ for the indicator of a clopen set $U\subseteq X$. Our conventions are $(Tx)_n=x_{n+1}$
> and $R=\LC(X,\F_2)\rtimes_T\Z=\{\sum_j f_ju^j:\text{finite sums}\}$, $ufu^{-1}=f\circ T^{-1}$,
> where $\LC$ denotes locally constant functions. Thus $ue_Uu^{-1}=e_{TU}$.
> Minimality and infiniteness imply that $T$ has no periodic points.
> For each $L$, every point therefore has a clopen neighborhood $U$ with $U\cap T^jU=\varnothing$
> for $0<|j|\le L$. Compactness gives finite clopen partitions with this property, refining any
> prescribed clopen partition.

The ring `R` is chain-core's `ClopenCrossedProduct T (ZMod 2)`. Its Laurent form is
`exists_sum_coeff_mul_unit_zpow`, and `ufu⁻¹ = f ∘ T⁻¹` is `unit_mul_coeff_mul_inv`. The statements
below hold for every homeomorphism `T` of a space `Y`, with the printed hypotheses on `Y` added where
they are used. The subshift `X ⊆ A^ℤ` with the shift is one such system.

* `IsMinimalSystem T`: every orbit is dense;
* `eU`, `unit_mul_eU_mul_inv`: `e_U` and `u e_U u⁻¹ = e_{TU}` (tex 70–77);
* `zpow_apply_ne_self`: an infinite minimal system has no periodic points (tex 78);
* `exists_clopen_nbhd_disjoint_translates`: clopen neighbourhoods `U` with `U ∩ T^jU = ∅` for
  `0 < |j| ≤ L` (tex 79–80);
* `exists_clopen_partition_disjoint_translates`: finite clopen partitions with this property,
  refining a prescribed finite clopen partition (tex 80–82).
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open ClopenCrossedProduct

section Minimal

variable {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y)

/-- A minimal system: every orbit is dense. -/
def IsMinimalSystem : Prop :=
  ∀ y : Y, Dense (Set.range fun j : ℤ => (T ^ j) y)

theorem zpow_mul_apply_eq_self {j : ℤ} {y : Y} (hy : (T ^ j) y = y) (q : ℤ) :
    (T ^ (j * q)) y = y := by
  rw [zpow_mul]
  induction q using Int.induction_on with
  | zero => rw [zpow_zero, Homeomorph.one_apply]
  | succ i ih => rw [zpow_add_one, Homeomorph.mul_apply, hy, ih]
  | pred i ih =>
    have hinv : (T ^ j)⁻¹ y = y := by
      calc (T ^ j)⁻¹ y = (T ^ j)⁻¹ ((T ^ j) y) := by rw [hy]
        _ = y := by rw [Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
    rw [zpow_sub_one, Homeomorph.mul_apply, hinv, ih]

theorem zpow_apply_eq_zpow_emod {j : ℤ} {y : Y} (hy : (T ^ j) y = y) (i : ℤ) :
    (T ^ i) y = (T ^ (i % j)) y := by
  conv_lhs => rw [← Int.emod_add_mul_ediv i j]
  rw [zpow_add, Homeomorph.mul_apply, zpow_mul_apply_eq_self T hy]

/-- **No periodic points** (tex 78): "Minimality and infiniteness imply that $T$ has no periodic
points." -/
theorem zpow_apply_ne_self [T2Space Y] [Infinite Y] (hmin : IsMinimalSystem T) {j : ℤ} (hj : j ≠ 0)
    (y : Y) : (T ^ j) y ≠ y := by
  intro hy
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Finset Y,
      S = (Finset.range j.natAbs).image fun n : ℕ => (T ^ (n : ℤ)) y := ⟨_, rfl⟩
  have hsub : Set.range (fun i : ℤ => (T ^ i) y) ⊆ (S : Set Y) := by
    rintro _ ⟨i, rfl⟩
    show (T ^ i) y ∈ (S : Set Y)
    rw [zpow_apply_eq_zpow_emod T hy i, hSdef]
    have h0 : 0 ≤ i % j := Int.emod_nonneg i hj
    have h1 : i % j < |j| := Int.emod_lt_abs i hj
    rw [Int.abs_eq_natAbs] at h1
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i % j).toNat, Finset.mem_range.2 (by omega), ?_⟩)
    rw [Int.toNat_of_nonneg h0]
  have huniv : (Set.univ : Set Y) ⊆ S := by
    rw [← (hmin y).closure_eq]
    exact closure_minimal hsub S.finite_toSet.isClosed
  exact Set.infinite_univ (S.finite_toSet.subset huniv)

/-- **Clopen neighbourhoods with disjoint translates** (tex 79–80): "For each $L$, every point
therefore has a clopen neighborhood $U$ with $U\cap T^jU=\varnothing$ for $0<|j|\le L$." -/
theorem exists_clopen_nbhd_disjoint_translates [TotallySeparatedSpace Y]
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : Y, (T ^ j) y ≠ y) (L : ℕ) (y : Y) :
    ∃ U : Set Y, IsClopen U ∧ y ∈ U ∧
      ∀ j : ℤ, j ≠ 0 → |j| ≤ L → Disjoint U (⇑(T ^ j) '' U) := by
  classical
  have hsep : ∀ j : ℤ, ∃ C : Set Y, IsClopen C ∧ y ∈ C ∧ (j ≠ 0 → (T ^ j) y ∉ C) := by
    intro j
    by_cases hj : j = 0
    · exact ⟨Set.univ, isClopen_univ, Set.mem_univ y, fun h => absurd hj h⟩
    · obtain ⟨C, hC, hyC, hTC⟩ := exists_isClopen_of_totally_separated (hfree j hj y).symm
      exact ⟨C, hC, hyC, fun _ => hTC⟩
  choose C hC hyC hTC using hsep
  obtain ⟨F, hFdef⟩ : ∃ F : Finset ℤ, F = (Finset.Icc (-(L : ℤ)) L).erase 0 := ⟨_, rfl⟩
  refine ⟨⋂ j ∈ F, (C j ∩ ⇑(T ^ j) ⁻¹' (C j)ᶜ),
    isClopen_biInter_finset fun j _ => (hC j).inter ((hC j).compl.preimage (T ^ j).continuous),
    Set.mem_iInter₂.2 fun j hj => ⟨hyC j, hTC j (by rw [hFdef] at hj; exact Finset.ne_of_mem_erase hj)⟩,
    fun j hj0 hjL => ?_⟩
  have hjF : j ∈ F := by
    rw [hFdef]
    obtain ⟨h1, h2⟩ := abs_le.1 hjL
    exact Finset.mem_erase.2 ⟨hj0, Finset.mem_Icc.2 ⟨h1, h2⟩⟩
  rw [Set.disjoint_left]
  rintro _ hz ⟨w, hw, rfl⟩
  exact (Set.mem_iInter₂.1 hw j hjF).2 (Set.mem_iInter₂.1 hz j hjF).1

/-- **Refining clopen partitions with disjoint translates** (tex 80–82): "Compactness gives finite
clopen partitions with this property, refining any prescribed clopen partition." The pieces are
indexed by `Fin n × Fin p`, and the piece `Q i a` lies in the prescribed atom `P a`. -/
theorem exists_clopen_partition_disjoint_translates [CompactSpace Y] [TotallySeparatedSpace Y]
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : Y, (T ^ j) y ≠ y) (L : ℕ) {p : ℕ} (P : Fin p → Set Y)
    (hPc : ∀ a, IsClopen (P a)) (hPdisj : ∀ a b, a ≠ b → Disjoint (P a) (P b))
    (hPcov : ∀ y, ∃ a, y ∈ P a) :
    ∃ (n : ℕ) (Q : Fin n → Fin p → Set Y), (∀ i a, IsClopen (Q i a)) ∧
      (∀ i a i' a', (i, a) ≠ (i', a') → Disjoint (Q i a) (Q i' a')) ∧
      (∀ y, ∃ i a, y ∈ Q i a) ∧ (∀ i a, Q i a ⊆ P a) ∧
      ∀ i a (j : ℤ), j ≠ 0 → |j| ≤ L → Disjoint (Q i a) (⇑(T ^ j) '' Q i a) := by
  classical
  choose U hUc hyU hUdisj using exists_clopen_nbhd_disjoint_translates T hfree L
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun y => (hUc y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Fin t.card → Set Y, W = fun i => U (t.equivFin.symm i).1 := ⟨_, rfl⟩
  have hWc : ∀ i, IsClopen (W i) := fun i => by rw [hWdef]; exact hUc _
  have hWcov : (Set.univ : Set Y) ⊆ ⋃ i, W i := by
    intro y _
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨s, hs⟩, ?_⟩
    rw [hWdef]
    simpa only [Equiv.symm_apply_apply] using hys
  refine ⟨t.card, fun i a => Dynamics.coverPiece W Set.univ i ∩ P a,
    fun i a => (Dynamics.isClopen_coverPiece W Set.univ isClopen_univ hWc i).inter (hPc a),
    fun i a i' a' hne => ?_, fun y => ?_, fun i a => Set.inter_subset_right,
    fun i a j hj0 hjL => ?_⟩
  · by_cases hii : i = i'
    · subst hii
      have haa : a ≠ a' := fun h => hne (by rw [h])
      exact (hPdisj a a' haa).mono Set.inter_subset_right Set.inter_subset_right
    · exact (Dynamics.disjoint_coverPiece W Set.univ hii).mono Set.inter_subset_left
        Set.inter_subset_left
  · obtain ⟨i, hi⟩ := Dynamics.exists_mem_coverPiece W Set.univ hWcov (Set.mem_univ y)
    obtain ⟨a, ha⟩ := hPcov y
    exact ⟨i, a, hi, ha⟩
  · have hsubU : Dynamics.coverPiece W Set.univ i ∩ P a ⊆ U (t.equivFin.symm i).1 := by
      intro z hz
      have h := (Dynamics.coverPiece_subset W Set.univ i hz.1).2
      rw [hWdef] at h
      exact h
    exact (hUdisj _ j hj0 hjL).mono hsubU (Set.image_mono hsubU)

end Minimal

section Ring

variable {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y) (k : Type*) [Ring k]

/-- `e_U`, the indicator of a clopen set `U` as an element of `R` (tex 70). -/
noncomputable def eU {U : Set Y} (hU : IsClopen U) : ClopenCrossedProduct T k :=
  coeff T k (LocallyConstant.charFn k hU)

/-- **`u e_U u⁻¹ = e_{TU}`** (tex 77). -/
theorem unit_mul_eU_mul_inv {U : Set Y} (hU : IsClopen U) :
    (unit T k : ClopenCrossedProduct T k) * eU T k hU * ↑(unit T k)⁻¹ =
      eU T k (isClopen_image T hU) :=
  (unit_mul_coeff_mul_inv T k _).trans (congrArg (coeff T k) (comap_symm_charFn k T hU))

end Ring

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.zpow_apply_ne_self
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_clopen_nbhd_disjoint_translates
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_clopen_partition_disjoint_translates
#audit_axioms GroupApproximation.SimpleKazhdanSofic.unit_mul_eU_mul_inv
