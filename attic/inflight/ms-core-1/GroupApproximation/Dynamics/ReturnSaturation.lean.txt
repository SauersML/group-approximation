import GroupApproximation.Dynamics.FirstReturnMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Saturating an induced subsystem through the return towers

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1745–1749:

> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.  Theorem~\ref{thm:core-ring-reflection}
> applied to this subsystem makes every one of its points chain recurrent
> in $X$, proving the reverse inclusion.

For a return section `C` of `T` (`IsReturnSection T r C`) and a set `Z ⊆ C` invariant under the
first-return map `S_C`:

* `mem_of_zpow_mem`: a point of `C` on the `T`-orbit of `z ∈ Z` lies in `Z`.  Visits of an orbit to
  `C` are exactly the successive returns, forward and backward (`mem_of_zpow_nat_mem`,
  `mem_of_zpow_neg_nat_mem`).
* `returnSaturation T C Z`: the union of the `T`-orbits of the points of `Z`, with
  `image_returnSaturation` (invariant) and `mem_returnSaturation_iff` (its trace on `C` is `Z`).
* `returnSaturation_eq_biUnion`: the saturation is the finite union `⋃_{i<2r} T^i(Z)` of the tower
  levels over `Z`, so it is closed when `X` is compact and `Z` is closed (`isClosed_returnSaturation`).
-/

namespace GroupApproximation.ChainCore

open Set

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X}

section Visits

variable (hC : IsReturnSection T r C) {Z : Set C}
  (hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Z ↔ z ∈ Z)

include hZ in
/-- Forward visits of an orbit to `C` stay in an `S_C`-invariant set. -/
theorem mem_of_zpow_nat_mem :
    ∀ (n : ℕ) (z : C), z ∈ Z → ∀ hn : (T ^ (n : ℤ)) (z : X) ∈ C,
      (⟨(T ^ (n : ℤ)) (z : X), hn⟩ : C) ∈ Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz hnC
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (⟨(T ^ ((0 : ℕ) : ℤ)) (z : X), hnC⟩ : C) = z := by
        refine Subtype.ext ?_
        show (T ^ ((0 : ℕ) : ℤ)) (z : X) = (z : X)
        rw [Nat.cast_zero, zpow_zero, Homeomorph.one_apply]
      rw [h0]
      exact hz
    · have hle : returnTime T C z ≤ n := returnTime_le_of_mem hC z hn hnC
      have hpos := (returnTime_spec hC (z : X)).1
      have heq : (T ^ ((n - returnTime T C z : ℕ) : ℤ)) (firstReturnHomeomorph hC z : X) =
          (T ^ (n : ℤ)) (z : X) := by
        rw [firstReturnHomeomorph_apply, ← Homeomorph.mul_apply, ← zpow_add, ← Nat.cast_add,
          Nat.sub_add_cancel hle]
      have hC' : (T ^ ((n - returnTime T C z : ℕ) : ℤ)) (firstReturnHomeomorph hC z : X) ∈ C := by
        rw [heq]
        exact hnC
      have h1 := ih (n - returnTime T C z) (by omega) (firstReturnHomeomorph hC z) ((hZ z).2 hz) hC'
      have h2 : (⟨(T ^ ((n - returnTime T C z : ℕ) : ℤ)) (firstReturnHomeomorph hC z : X), hC'⟩ :
          C) = ⟨(T ^ (n : ℤ)) (z : X), hnC⟩ := Subtype.ext heq
      rwa [h2] at h1

include hZ in
/-- Backward visits of an orbit to `C` stay in an `S_C`-invariant set. -/
theorem mem_of_zpow_neg_nat_mem :
    ∀ (n : ℕ) (z : C), z ∈ Z → ∀ hn : (T ^ (-(n : ℤ))) (z : X) ∈ C,
      (⟨(T ^ (-(n : ℤ))) (z : X), hn⟩ : C) ∈ Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz hnC
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (⟨(T ^ (-((0 : ℕ) : ℤ))) (z : X), hnC⟩ : C) = z := by
        refine Subtype.ext ?_
        show (T ^ (-((0 : ℕ) : ℤ))) (z : X) = (z : X)
        rw [Nat.cast_zero, neg_zero, zpow_zero, Homeomorph.one_apply]
      rw [h0]
      exact hz
    · have hnC' : ((T⁻¹) ^ (n : ℤ)) (z : X) ∈ C := by
        rw [inv_zpow, ← zpow_neg]
        exact hnC
      have hle : returnTime T⁻¹ C z ≤ n := returnTime_le_of_mem hC.inv z hn hnC'
      have hpos := (returnTime_spec hC.inv (z : X)).1
      have hs : (firstReturnHomeomorph hC).symm z ∈ Z :=
        (hZ _).1 (by rw [Homeomorph.apply_symm_apply]; exact hz)
      have heq : (T ^ (-((n - returnTime T⁻¹ C z : ℕ) : ℤ)))
          ((firstReturnHomeomorph hC).symm z : X) = (T ^ (-(n : ℤ))) (z : X) := by
        rw [firstReturnHomeomorph_symm_apply, inv_zpow, ← zpow_neg, ← Homeomorph.mul_apply,
          ← zpow_add, ← neg_add, ← Nat.cast_add, Nat.sub_add_cancel hle]
      have hC' : (T ^ (-((n - returnTime T⁻¹ C z : ℕ) : ℤ)))
          ((firstReturnHomeomorph hC).symm z : X) ∈ C := by
        rw [heq]
        exact hnC
      have h1 := ih (n - returnTime T⁻¹ C z) (by omega) ((firstReturnHomeomorph hC).symm z) hs hC'
      have h2 : (⟨(T ^ (-((n - returnTime T⁻¹ C z : ℕ) : ℤ)))
          ((firstReturnHomeomorph hC).symm z : X), hC'⟩ : C) =
          ⟨(T ^ (-(n : ℤ))) (z : X), hnC⟩ := Subtype.ext heq
      rwa [h2] at h1

include hZ in
/-- **Visits of an orbit to `C` are its successive returns**: a point of `C` on the `T`-orbit of
`z ∈ Z` lies in `Z`. -/
theorem mem_of_zpow_mem {z : C} (hz : z ∈ Z) (j : ℤ) (hj : (T ^ j) (z : X) ∈ C) :
    (⟨(T ^ j) (z : X), hj⟩ : C) ∈ Z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · exact mem_of_zpow_nat_mem hC hZ n z hz hj
  · exact mem_of_zpow_neg_nat_mem hC hZ n z hz hj

end Visits

/-- **The saturation of `Z ⊆ C` through the towers**: the union of the `T`-orbits of the points
of `Z`. -/
def returnSaturation (T : X ≃ₜ X) (C : Set X) (Z : Set C) : Set X :=
  {x | ∃ j : ℤ, ∃ z ∈ Z, (T ^ j) (z : X) = x}

theorem subset_returnSaturation {Z : Set C} (z : C) (hz : z ∈ Z) :
    (z : X) ∈ returnSaturation T C Z :=
  ⟨0, z, hz, by rw [zpow_zero, Homeomorph.one_apply]⟩

/-- The saturation is invariant. -/
theorem image_returnSaturation (Z : Set C) :
    T '' returnSaturation T C Z = returnSaturation T C Z := by
  ext x
  constructor
  · rintro ⟨y, ⟨j, z, hz, rfl⟩, rfl⟩
    exact ⟨1 + j, z, hz, by rw [zpow_one_add, Homeomorph.mul_apply]⟩
  · rintro ⟨j, z, hz, rfl⟩
    have h1 : 1 + (j - 1) = j := by omega
    exact ⟨(T ^ (j - 1)) (z : X), ⟨j - 1, z, hz, rfl⟩,
      by rw [← Homeomorph.mul_apply, ← zpow_one_add, h1]⟩

section Trace

variable (hC : IsReturnSection T r C) {Z : Set C}
  (hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Z ↔ z ∈ Z)

include hZ in
/-- **The trace of the saturation on `C` is `Z`.** -/
theorem mem_returnSaturation_iff (w : C) : (w : X) ∈ returnSaturation T C Z ↔ w ∈ Z := by
  constructor
  · rintro ⟨j, z, hz, hzw⟩
    have hj : (T ^ j) (z : X) ∈ C := by
      rw [hzw]
      exact w.2
    have h := mem_of_zpow_mem hC hZ hz j hj
    have hw : (⟨(T ^ j) (z : X), hj⟩ : C) = w := Subtype.ext hzw
    rwa [hw] at h
  · intro hw
    exact subset_returnSaturation w hw

include hZ in
/-- **The saturation is the finite union of the tower levels over `Z`.** -/
theorem returnSaturation_eq_biUnion :
    returnSaturation T C Z = ⋃ i ∈ Finset.range (2 * r), (T ^ (i : ℤ)) '' (Subtype.val '' Z) := by
  ext x
  constructor
  · rintro ⟨j, z, hz, rfl⟩
    obtain ⟨n, hn₁, hn₂, hnC⟩ := hC.inv.exists_return ((T ^ j) (z : X))
    have hc : (T ^ (j - n)) (z : X) ∈ C := by
      rwa [inv_zpow, ← zpow_neg, ← Homeomorph.mul_apply, ← zpow_add, neg_add_eq_sub] at hnC
    have hsum : (n : ℤ) + (j - n) = j := by omega
    refine Set.mem_iUnion₂.2 ⟨n, Finset.mem_range.2 (by omega),
      (T ^ (j - n)) (z : X), ⟨⟨_, hc⟩, mem_of_zpow_mem hC hZ hz (j - n) hc, rfl⟩, ?_⟩
    rw [← Homeomorph.mul_apply, ← zpow_add, hsum]
  · intro hx
    obtain ⟨i, -, y, ⟨z, hz, rfl⟩, rfl⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨i, z, hz, rfl⟩

include hZ in
/-- **The saturation of a closed set is closed.** -/
theorem isClosed_returnSaturation [CompactSpace X] [T2Space X] (hZc : IsClosed Z) :
    IsClosed (returnSaturation T C Z) := by
  rw [returnSaturation_eq_biUnion hC hZ]
  refine isClosed_biUnion_finset fun i _ => ?_
  have hcpt : IsCompact (Subtype.val '' Z) :=
    (hC.isClopen.isClosed.isClosedEmbedding_subtypeVal.isClosedMap Z hZc).isCompact
  exact (hcpt.image (T ^ (i : ℤ)).continuous).isClosed

end Trace

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_axioms mem_of_zpow_mem
#audit_axioms image_returnSaturation
#audit_axioms mem_returnSaturation_iff
#audit_axioms isClosed_returnSaturation
