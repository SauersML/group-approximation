import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiExponents
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerPerm
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# The local eight-level tower

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  Let `T` be an infinite minimal homeomorphism of a compact totally
separated space, `V` a nonempty clopen set and `f ∈ [[T]]` with `f x ≠ x` and `f (f x) ≠ x`.
Then `x` has a clopen neighbourhood `W` and there are exponents `E : Fin 8 → ℤ` with `E 0 = 0`
such that every `A ⊆ W` is the base of an eight-level tower along `T`, `f` and `f²` act on `W` as
`T ^ E 1` and `T ^ E 2`, and levels `3, …, 7` above `W` lie in `V` (`exists_local_eight_tower`).
-/

variable {X : Type*}

/-- **Local eight-level tower** around a point moved by `f` and `f²`. -/
theorem exists_local_eight_tower [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {V : Set X} (hV : IsClopen V)
    (hVne : V.Nonempty) {f : Equiv.Perm X} (hf : f ∈ fullGroup T) {x : X}
    (hx1 : f x ≠ x) (hx2 : f (f x) ≠ x) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ ∃ E : Fin 8 → ℤ, E 0 = 0 ∧
      (∀ A : Set X, A ⊆ W → ∀ i j y, (T.toEquiv ^ (-E i)) y ∈ A →
        (T.toEquiv ^ (-E j)) y ∈ A → i = j) ∧
      (∀ y ∈ W, f y = (T.toEquiv ^ E 1) y) ∧ (∀ y ∈ W, (f * f) y = (T.toEquiv ^ E 2) y) ∧
      (∀ i : Fin 8, 3 ≤ (i : ℕ) → ∀ y, (T.toEquiv ^ (-E i)) y ∈ W → y ∈ V) := by
  obtain ⟨n, hn, hfn⟩ := mem_fullGroup.mp hf
  have hff : ∀ y, f (f y) = (T ^ (n (f y) + n y)) y := fun y => by
    rw [← zpow_apply_zpow_apply, ← hfn y, ← hfn (f y)]
  have ha : n x ≠ 0 := fun h => hx1 (by rw [hfn x, h, zpow_zero, Homeomorph.one_apply])
  have hc : n (f x) + n x ≠ 0 := fun h =>
    hx2 (by rw [hff x, h, zpow_zero, Homeomorph.one_apply])
  have hac : n x ≠ n (f x) + n x := fun h =>
    hx1 (f.injective (by rw [hff x, ← h, ← hfn x]))
  obtain ⟨E, m, hE0, hE1, hE2, hinj, hmV, hEm⟩ :=
    exists_eight_exponents T hmin hV.isOpen hVne x ha hc hac
  have hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y := fun j hj y =>
    SimpleKazhdanSofic.zpow_apply_ne_self T hmin hj y
  have hL : ∀ i j : Fin 8,
      |E j - E i| ≤ ((∑ p : Fin 8, ∑ q : Fin 8, (E p - E q).natAbs : ℕ) : ℤ) := fun i j => by
    rw [← Int.natCast_natAbs]
    refine Nat.cast_le.mpr (le_trans ?_ (Finset.single_le_sum
      (f := fun p => ∑ q : Fin 8, (E p - E q).natAbs) (fun p _ => Nat.zero_le _)
      (Finset.mem_univ j)))
    exact Finset.single_le_sum (f := fun q => (E j - E q).natAbs) (fun q _ => Nat.zero_le _)
      (Finset.mem_univ i)
  obtain ⟨C, hCc, hxC, hC⟩ := SimpleKazhdanSofic.exists_clopen_nbhd_disjoint_translates T hfree
    (∑ p : Fin 8, ∑ q : Fin 8, (E p - E q).natAbs) x
  have hfc : Continuous f := IsFullGroupElement.continuous (mem_fullGroup.mp hf)
  refine ⟨C ∩ n ⁻¹' {n x} ∩ ⇑f ⁻¹' (n ⁻¹' {n (f x)}) ∩ ⋂ j : Fin 5, ⇑(T ^ m j) ⁻¹' V,
    ((hCc.inter ((isClopen_discrete {n x}).preimage hn)).inter
      (((isClopen_discrete {n (f x)}).preimage hn).preimage hfc)).inter
      (isClopen_iInter_of_finite fun j => hV.preimage (T ^ m j).continuous),
    ⟨⟨⟨hxC, Set.mem_singleton _⟩, Set.mem_singleton _⟩, Set.mem_iInter.mpr hmV⟩,
    E, hE0, ?_, ?_, ?_, ?_⟩
  · intro A hAW i j y hi hj
    by_contra hij
    have hw₁ : (T ^ (-E i)) y ∈ C := by
      rw [← toEquiv_zpow_apply]
      exact (hAW hi).1.1.1
    have hw₂ : (T ^ (-E j)) y ∈ C := by
      rw [← toEquiv_zpow_apply]
      exact (hAW hj).1.1.1
    have heq : (T ^ (E j - E i)) ((T ^ (-E j)) y) = (T ^ (-E i)) y := by
      rw [zpow_apply_zpow_apply, show E j - E i + -E j = -E i by ring]
    have hk0 : E j - E i ≠ 0 := sub_ne_zero.mpr fun h => hij (hinj h).symm
    exact Set.disjoint_left.mp (hC (E j - E i) hk0 (hL i j)) hw₁ ⟨(T ^ (-E j)) y, hw₂, heq⟩
  · intro y hy
    have hny : n y = n x := hy.1.1.2
    rw [hE1, toEquiv_zpow_apply, hfn y, hny]
  · intro y hy
    have hny : n y = n x := hy.1.1.2
    have hnfy : n (f y) = n (f x) := hy.1.2
    rw [hE2, toEquiv_zpow_apply, Equiv.Perm.mul_apply, hff y, hny, hnfy]
  · intro i hi y hy
    obtain ⟨j, hj⟩ := hEm i hi
    have hyj : (T ^ m j) ((T.toEquiv ^ (-E i)) y) ∈ V := Set.mem_iInter.mp hy.2 j
    rwa [hj, toEquiv_zpow_apply, zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
      Homeomorph.one_apply] at hyj

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_local_eight_tower
