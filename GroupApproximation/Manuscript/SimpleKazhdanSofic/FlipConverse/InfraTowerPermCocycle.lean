import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 1: the cocycle and the pointwise map

Infrastructure for census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the key is absent from the current tex, so there is no line number).  Lane sk-flip-04:
permutations of the levels of a clopen tower embed in `[[T]]`.

Setting.  `T : X ≃ₜ X`, `V ⊆ X` clopen, exponents `k : Fin n → ℤ`, and the levels `T^{k i} V`
pairwise disjoint.  The exponents are arbitrary so that the towers of lane sk-flip-03
(`exists_isClopen_tower_in_open`) apply; the consecutive case `k i = i` is in `InfraTowerPerm`.
For `π ∈ Sym(n)`:

* `towerCocycle T V k π z = ∑_i [T^{-k i} z ∈ V] (k (π i) - k i)`.  Each summand is the indicator
  of the clopen set `T^{k i} V` times a constant, so the cocycle is continuous.  By disjointness
  at most one summand is nonzero: on `T^{k i} V` it is `k (π i) - k i`, off the tower it is `0`.
* `towerFun T V k π z = T^{towerCocycle z} z`: on level `i`, `T^{k i} v ↦ T^{k (π i)} v`; off the
  tower it is the identity (`towerFun_of_mem`, `towerFun_level`, `towerFun_of_notMem`).
* `towerFun_one`, `towerFun_mul`: the action law `towerFun (π σ) = towerFun π ∘ towerFun σ`,
  checked level by level (`T^{k i} v ↦ T^{k (σ i)} v ↦ T^{k (π (σ i))} v`) and trivially off the
  tower.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

theorem homeoPow_neg_apply_homeoPow_apply (T : X ≃ₜ X) (m : ℤ) (x : X) :
    (T ^ (-m)) ((T ^ m) x) = x := by
  rw [← homeoPow_add, neg_add_cancel, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.homeoPow_neg_apply_homeoPow_apply

theorem homeoPow_apply_homeoPow_neg_apply (T : X ≃ₜ X) (m : ℤ) (x : X) :
    (T ^ m) ((T ^ (-m)) x) = x := by
  rw [← homeoPow_add, add_neg_cancel, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.homeoPow_apply_homeoPow_neg_apply

theorem mem_image_homeoPow_iff (T : X ≃ₜ X) (m : ℤ) (V : Set X) (z : X) :
    z ∈ (T ^ m) '' V ↔ (T ^ (-m)) z ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [homeoPow_neg_apply_homeoPow_apply]
    exact hv
  · intro h
    exact ⟨(T ^ (-m)) z, h, homeoPow_apply_homeoPow_neg_apply T m z⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_image_homeoPow_iff

open Classical in
/-- The cocycle of the tower permutation `π`: `k (π i) - k i` on level `T^{k i} V`, `0` off the
tower. -/
noncomputable def towerCocycle (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ)
    (π : Equiv.Perm (Fin n)) (z : X) : ℤ :=
  ∑ i : Fin n, if (T ^ (-k i)) z ∈ V then k (π i) - k i else 0

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle

theorem towerCocycle_of_mem (T : X ≃ₜ X) {V : Set X} {n : ℕ} {k : Fin n → ℤ}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {z : X} (hz : (T ^ (-k i)) z ∈ V) :
    towerCocycle T V k π z = k (π i) - k i := by
  classical
  have h₀ : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
      (if (T ^ (-k j)) z ∈ V then k (π j) - k j else 0) = 0 := by
    intro j _ hji
    refine if_neg fun hj => ?_
    exact Set.disjoint_left.1 (hdisj i j hji.symm) ((mem_image_homeoPow_iff T (k i) V z).2 hz)
      ((mem_image_homeoPow_iff T (k j) V z).2 hj)
  rw [towerCocycle, Finset.sum_eq_single i h₀ fun h => absurd (Finset.mem_univ i) h, if_pos hz]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle_of_mem

theorem towerCocycle_of_notMem (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ)
    (π : Equiv.Perm (Fin n)) {z : X} (hz : ∀ i : Fin n, (T ^ (-k i)) z ∉ V) :
    towerCocycle T V k π z = 0 := by
  classical
  rw [towerCocycle]
  exact Finset.sum_eq_zero fun i _ => if_neg (hz i)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerCocycle_of_notMem

theorem continuous_towerCocycle (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) {n : ℕ}
    (k : Fin n → ℤ) (π : Equiv.Perm (Fin n)) : Continuous (towerCocycle T V k π) := by
  classical
  have h : ∀ i : Fin n, Continuous fun z : X =>
      if (T ^ (-k i)) z ∈ V then k (π i) - k i else 0 := by
    intro i
    have hfr : frontier {z : X | (T ^ (-k i)) z ∈ V} = ∅ :=
      isClopen_iff_frontier_eq_empty.1 (hV.preimage (T ^ (-k i)).continuous)
    refine Continuous.if (fun a ha => ?_) continuous_const continuous_const
    have h0 : a ∈ (∅ : Set X) := by
      rw [← hfr]
      exact ha
    exact absurd h0 (Set.notMem_empty a)
  have hsum := continuous_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => h i
  exact hsum

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_towerCocycle

/-- The pointwise tower permutation: `T^{k i} v ↦ T^{k (π i)} v` on the levels, identity
elsewhere. -/
noncomputable def towerFun (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ)
    (π : Equiv.Perm (Fin n)) (z : X) : X :=
  (T ^ towerCocycle T V k π z) z

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun

theorem continuous_towerFun (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) {n : ℕ}
    (k : Fin n → ℤ) (π : Equiv.Perm (Fin n)) : Continuous (towerFun T V k π) :=
  continuous_hpow_apply T (continuous_towerCocycle T hV k π)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_towerFun

theorem towerFun_of_mem (T : X ≃ₜ X) {V : Set X} {n : ℕ} {k : Fin n → ℤ}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {z : X} (hz : (T ^ (-k i)) z ∈ V) :
    towerFun T V k π z = (T ^ k (π i)) ((T ^ (-k i)) z) := by
  rw [towerFun, towerCocycle_of_mem T hdisj π i hz, ← homeoPow_add, sub_eq_add_neg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_of_mem

theorem towerFun_level (T : X ≃ₜ X) {V : Set X} {n : ℕ} {k : Fin n → ℤ}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {v : X} (hv : v ∈ V) :
    towerFun T V k π ((T ^ k i) v) = (T ^ k (π i)) v := by
  have hz : (T ^ (-k i)) ((T ^ k i) v) ∈ V := by
    rw [homeoPow_neg_apply_homeoPow_apply]
    exact hv
  rw [towerFun_of_mem T hdisj π i hz, homeoPow_neg_apply_homeoPow_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_level

theorem towerFun_of_notMem (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ)
    (π : Equiv.Perm (Fin n)) {z : X} (hz : ∀ i : Fin n, (T ^ (-k i)) z ∉ V) :
    towerFun T V k π z = z := by
  rw [towerFun, towerCocycle_of_notMem T V k π hz, homeoPow_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_of_notMem

theorem towerFun_one (T : X ≃ₜ X) {V : Set X} {n : ℕ} {k : Fin n → ℤ}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V)) (z : X) :
    towerFun T V k (1 : Equiv.Perm (Fin n)) z = z := by
  by_cases h : ∃ i : Fin n, (T ^ (-k i)) z ∈ V
  · obtain ⟨i, hi⟩ := h
    rw [towerFun_of_mem T hdisj 1 i hi, Equiv.Perm.one_apply, homeoPow_apply_homeoPow_neg_apply]
  · push Not at h
    exact towerFun_of_notMem T V k 1 h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_one

theorem towerFun_mul (T : X ≃ₜ X) {V : Set X} {n : ℕ} {k : Fin n → ℤ}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π σ : Equiv.Perm (Fin n)) (z : X) :
    towerFun T V k (π * σ) z = towerFun T V k π (towerFun T V k σ z) := by
  by_cases h : ∃ i : Fin n, (T ^ (-k i)) z ∈ V
  · obtain ⟨i, hi⟩ := h
    have hlev : (T ^ (-k (σ i))) ((T ^ k (σ i)) ((T ^ (-k i)) z)) ∈ V := by
      rw [homeoPow_neg_apply_homeoPow_apply]
      exact hi
    rw [towerFun_of_mem T hdisj σ i hi, towerFun_of_mem T hdisj π (σ i) hlev,
      homeoPow_neg_apply_homeoPow_apply, towerFun_of_mem T hdisj (π * σ) i hi,
      Equiv.Perm.mul_apply]
  · push Not at h
    rw [towerFun_of_notMem T V k σ h, towerFun_of_notMem T V k π h,
      towerFun_of_notMem T V k (π * σ) h]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerFun_mul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
