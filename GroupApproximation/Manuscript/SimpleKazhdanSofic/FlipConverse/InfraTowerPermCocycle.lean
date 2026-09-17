import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 1: the cocycle and the pointwise map

Infrastructure for census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the key is absent from the current tex, so there is no line number).  Lane sk-flip-04:
permutations of the levels of a clopen tower embed in `[[T]]`.

Setting.  `T : X ≃ₜ X`, `V ⊆ X` clopen, `n : ℕ`, and the levels `T^i V` (`i < n`) pairwise
disjoint (the hypothesis shape produced by lane sk-flip-03).  For `π ∈ Sym(n)`:

* `towerCocycle T V π z = ∑_{i<n} [T^{-i} z ∈ V] (π i - i)`.  Each summand is the indicator of the
  clopen set `T^i V` times a constant, so the cocycle is continuous.  By disjointness at most one
  summand is nonzero: on `T^i V` it equals `π i - i`, off the tower it is `0`.
* `towerFun T V π z = T^{towerCocycle z} z`; on level `i`, `T^i v ↦ T^{π i} v`, off the tower it is
  the identity (`towerFun_of_mem`, `towerFun_level`, `towerFun_of_notMem`).
* `towerFun_one`, `towerFun_mul`: the action law `towerFun (π σ) = towerFun π ∘ towerFun σ`,
  checked level by level (`T^i v ↦ T^{σ i} v ↦ T^{π (σ i)} v`) and trivially off the tower.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

theorem homeoPow_neg_apply_homeoPow_apply (T : X ≃ₜ X) (k : ℤ) (x : X) :
    (T ^ (-k)) ((T ^ k) x) = x := by
  rw [← homeoPow_add, neg_add_cancel, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.homeoPow_neg_apply_homeoPow_apply

theorem homeoPow_apply_homeoPow_neg_apply (T : X ≃ₜ X) (k : ℤ) (x : X) :
    (T ^ k) ((T ^ (-k)) x) = x := by
  rw [← homeoPow_add, add_neg_cancel, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.homeoPow_apply_homeoPow_neg_apply

theorem mem_image_homeoPow_iff (T : X ≃ₜ X) (k : ℤ) (V : Set X) (z : X) :
    z ∈ (T ^ k) '' V ↔ (T ^ (-k)) z ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [homeoPow_neg_apply_homeoPow_apply]
    exact hv
  · intro h
    exact ⟨(T ^ (-k)) z, h, homeoPow_apply_homeoPow_neg_apply T k z⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_image_homeoPow_iff

open Classical in
/-- The cocycle of the tower permutation `π`: `π i - i` on level `T^i V`, `0` off the tower. -/
noncomputable def towerCocycle (T : X ≃ₜ X) (V : Set X) {n : ℕ} (π : Equiv.Perm (Fin n))
    (z : X) : ℤ :=
  ∑ i : Fin n, if (T ^ (-((i : ℕ) : ℤ))) z ∈ V then ((π i : ℕ) : ℤ) - ((i : ℕ) : ℤ) else 0

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle

theorem towerCocycle_of_mem (T : X ≃ₜ X) {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {z : X} (hz : (T ^ (-((i : ℕ) : ℤ))) z ∈ V) :
    towerCocycle T V π z = ((π i : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by
  classical
  have h₀ : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
      (if (T ^ (-((j : ℕ) : ℤ))) z ∈ V then ((π j : ℕ) : ℤ) - ((j : ℕ) : ℤ) else 0) = 0 := by
    intro j _ hji
    refine if_neg fun hj => ?_
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h).symm
    exact Set.disjoint_left.1 (hdisj (i : ℕ) i.2 (j : ℕ) j.2 hij)
      ((mem_image_homeoPow_iff T ((i : ℕ) : ℤ) V z).2 hz)
      ((mem_image_homeoPow_iff T ((j : ℕ) : ℤ) V z).2 hj)
  rw [towerCocycle, Finset.sum_eq_single i h₀ fun h => absurd (Finset.mem_univ i) h, if_pos hz]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle_of_mem

theorem towerCocycle_of_notMem (T : X ≃ₜ X) (V : Set X) {n : ℕ} (π : Equiv.Perm (Fin n))
    {z : X} (hz : ∀ i : Fin n, (T ^ (-((i : ℕ) : ℤ))) z ∉ V) : towerCocycle T V π z = 0 := by
  classical
  rw [towerCocycle]
  exact Finset.sum_eq_zero fun i _ => if_neg (hz i)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle_of_notMem

theorem continuous_towerCocycle (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) {n : ℕ}
    (π : Equiv.Perm (Fin n)) : Continuous (towerCocycle T V π) := by
  classical
  have h : ∀ i : Fin n, Continuous fun z : X =>
      if (T ^ (-((i : ℕ) : ℤ))) z ∈ V then ((π i : ℕ) : ℤ) - ((i : ℕ) : ℤ) else 0 := by
    intro i
    have hfr : frontier {z : X | (T ^ (-((i : ℕ) : ℤ))) z ∈ V} = ∅ :=
      isClopen_iff_frontier_eq_empty.1 (hV.preimage (T ^ (-((i : ℕ) : ℤ))).continuous)
    refine Continuous.if (fun a ha => ?_) continuous_const continuous_const
    have h0 : a ∈ (∅ : Set X) := by
      rw [← hfr]
      exact ha
    exact absurd h0 (Set.notMem_empty a)
  have hsum := continuous_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => h i
  exact hsum

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_towerCocycle

/-- The pointwise tower permutation: `T^i v ↦ T^{π i} v` on the levels, identity elsewhere. -/
noncomputable def towerFun (T : X ≃ₜ X) (V : Set X) {n : ℕ} (π : Equiv.Perm (Fin n)) (z : X) :
    X :=
  (T ^ towerCocycle T V π z) z

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun

theorem continuous_towerFun (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) {n : ℕ}
    (π : Equiv.Perm (Fin n)) : Continuous (towerFun T V π) :=
  continuous_hpow_apply T (continuous_towerCocycle T hV π)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_towerFun

theorem towerFun_of_mem (T : X ≃ₜ X) {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {z : X} (hz : (T ^ (-((i : ℕ) : ℤ))) z ∈ V) :
    towerFun T V π z = (T ^ ((π i : ℕ) : ℤ)) ((T ^ (-((i : ℕ) : ℤ))) z) := by
  rw [towerFun, towerCocycle_of_mem T hdisj π i hz, ← homeoPow_add, sub_eq_add_neg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_of_mem

theorem towerFun_level (T : X ≃ₜ X) {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {v : X} (hv : v ∈ V) :
    towerFun T V π ((T ^ ((i : ℕ) : ℤ)) v) = (T ^ ((π i : ℕ) : ℤ)) v := by
  have hz : (T ^ (-((i : ℕ) : ℤ))) ((T ^ ((i : ℕ) : ℤ)) v) ∈ V := by
    rw [homeoPow_neg_apply_homeoPow_apply]
    exact hv
  rw [towerFun_of_mem T hdisj π i hz, homeoPow_neg_apply_homeoPow_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_level

theorem towerFun_of_notMem (T : X ≃ₜ X) (V : Set X) {n : ℕ} (π : Equiv.Perm (Fin n)) {z : X}
    (hz : ∀ i : Fin n, (T ^ (-((i : ℕ) : ℤ))) z ∉ V) : towerFun T V π z = z := by
  rw [towerFun, towerCocycle_of_notMem T V π hz, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_of_notMem

theorem towerFun_one (T : X ≃ₜ X) {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (z : X) : towerFun T V (1 : Equiv.Perm (Fin n)) z = z := by
  by_cases h : ∃ i : Fin n, (T ^ (-((i : ℕ) : ℤ))) z ∈ V
  · obtain ⟨i, hi⟩ := h
    rw [towerFun_of_mem T hdisj 1 i hi, Equiv.Perm.one_apply, homeoPow_apply_homeoPow_neg_apply]
  · push_neg at h
    exact towerFun_of_notMem T V 1 h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_one

theorem towerFun_mul (T : X ≃ₜ X) {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π σ : Equiv.Perm (Fin n)) (z : X) :
    towerFun T V (π * σ) z = towerFun T V π (towerFun T V σ z) := by
  by_cases h : ∃ i : Fin n, (T ^ (-((i : ℕ) : ℤ))) z ∈ V
  · obtain ⟨i, hi⟩ := h
    have hlev : (T ^ (-((σ i : ℕ) : ℤ)))
        ((T ^ ((σ i : ℕ) : ℤ)) ((T ^ (-((i : ℕ) : ℤ))) z)) ∈ V := by
      rw [homeoPow_neg_apply_homeoPow_apply]
      exact hi
    rw [towerFun_of_mem T hdisj σ i hi, towerFun_of_mem T hdisj π (σ i) hlev,
      homeoPow_neg_apply_homeoPow_apply, towerFun_of_mem T hdisj (π * σ) i hi,
      Equiv.Perm.mul_apply]
  · push_neg at h
    rw [towerFun_of_notMem T V σ h, towerFun_of_notMem T V π h,
      towerFun_of_notMem T V (π * σ) h]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_mul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
