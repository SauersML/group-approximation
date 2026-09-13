import Mathlib.Data.Int.Interval
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Dynamics.ReturnTowerStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# The return section of a system without short periods

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1709–1719:

> Choose a finite clopen cover $U_1,\dots,U_m$ with
> $U_i\cap T^jU_i=\varnothing$ for $0<|j|<r$.  Starting with $C_0=\varnothing$,
> put
> $C_i=C_{i-1}\cup\left(U_i\setminus\bigcup_{|j|<r}T^jC_{i-1}\right)$.
> Then $C=C_m$ is clopen, separated from its first $r-1$ translates,
> and $X=\bigcup_{|j|<r}T^jC$.  Its return gaps lie in $[r,2r-1]$:
> a larger gap would have a middle point at distance at least $r$
> from every return.  For $r=1$ simply take $C=X$.

* `exists_separated_clopen_cover`: the finite clopen cover, for compact Hausdorff totally
  disconnected `X` and `T` without points of period `< r`;
* `nearOrbit T r S = ⋃_{|j|<r} T^j S` and the printed recursion `sectionStep`;
* `isClopen_sectionStep`, `disjoint_sectionStep`, `subset_nearOrbit_sectionStep`, and so
  `exists_isReturnSection`;
* `returnTime_spec`, `returnTime_min`, `le_returnTime`, `returnTime_le`: the return gaps lie in
  `[r, 2r - 1]`; the upper bound comes from the middle point `T^r x`;
* `IsReturnSection.eq_univ_of_one`, `isReturnSection_univ_one`: for `r = 1`, `C = X`;
* the closed endpoint `returnSectionStatement_holds : ReturnSectionStatement`.
-/

namespace GroupApproximation.ChainCore

open Set

section Powers

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

theorem zpow_apply_zpow_apply_homeomorph (i j : ℤ) (x : X) :
    (T ^ i) ((T ^ j) x) = (T ^ (i + j)) x := by
  rw [zpow_add, Homeomorph.mul_apply]

theorem zpow_neg_apply_zpow_apply_homeomorph (j : ℤ) (x : X) : (T ^ (-j)) ((T ^ j) x) = x := by
  rw [zpow_apply_zpow_apply_homeomorph, neg_add_cancel, zpow_zero, Homeomorph.one_apply]

end Powers

/-! ### The separated clopen cover (tex 1709–1710) -/

section Cover

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] (T : X ≃ₜ X) {r : ℕ}

/-- Every point has a clopen neighbourhood `U` with `U ∩ T^j U = ∅` for `0 < j < r`. -/
theorem exists_isClopen_separated (hT : NoShortPeriods T r) (x : X) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      ∀ j : ℕ, 0 < j → j < r → Disjoint U ((T ^ (j : ℤ)) '' U) := by
  have hV : ∀ j : ℕ, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧
      (0 < j → j < r → (T ^ (j : ℤ)) x ∉ V) := by
    intro j
    by_cases hj : 0 < j ∧ j < r
    · obtain ⟨V, hVc, hxV, hVsub⟩ := compact_exists_isClopen_in_isOpen
        (isOpen_compl_singleton (x := (T ^ (j : ℤ)) x))
        (show x ∈ ({(T ^ (j : ℤ)) x} : Set X)ᶜ from fun h => hT x j hj.1 hj.2 h.symm)
      exact ⟨V, hVc, hxV, fun _ _ h => hVsub h rfl⟩
    · exact ⟨univ, isClopen_univ, mem_univ x, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hj⟩
  choose V hVc hxV hVn using hV
  refine ⟨⋂ j ∈ Finset.Ioo 0 r, V j ∩ (T ^ (j : ℤ)) ⁻¹' (V j)ᶜ, ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset fun j _ =>
      (hVc j).inter ((hVc j).compl.preimage (T ^ (j : ℤ)).continuous)
  · refine mem_iInter₂.2 fun j hj => ⟨hxV j, ?_⟩
    obtain ⟨h₁, h₂⟩ := Finset.mem_Ioo.1 hj
    exact hVn j h₁ h₂
  · intro j h₁ h₂
    refine disjoint_left.2 fun y hy hyimg => ?_
    obtain ⟨z, hz, rfl⟩ := hyimg
    have hjI : j ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨h₁, h₂⟩
    exact (mem_iInter₂.1 hz j hjI).2 (mem_iInter₂.1 hy j hjI).1

/-- **A finite clopen cover `U_1, …, U_m` with `U_i ∩ T^j U_i = ∅` for `0 < j < r`**
(tex 1709–1710). -/
theorem exists_separated_clopen_cover (hT : NoShortPeriods T r) :
    ∃ (m : ℕ) (U : Fin m → Set X), (∀ i, IsClopen (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
      ∀ i (j : ℕ), 0 < j → j < r → Disjoint (U i) ((T ^ (j : ℤ)) '' U i) := by
  choose W hWc hxW hWd using exists_isClopen_separated T hT
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W (fun x => (hWc x).isOpen)
    (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWc _, fun x => ?_, fun i => hWd _⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end Cover

/-! ### The recursion (tex 1710–1716) -/

section Recursion

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (r : ℕ)

/-- `⋃_{|j|<r} T^j S`. -/
def nearOrbit (S : Set X) : Set X :=
  ⋃ j ∈ Finset.Ioo (-(r : ℤ)) r, (T ^ j) '' S

theorem mem_nearOrbit {S : Set X} {x : X} :
    x ∈ nearOrbit T r S ↔ ∃ j : ℤ, |j| < r ∧ x ∈ (T ^ j) '' S := by
  simp only [nearOrbit, mem_iUnion₂, Finset.mem_Ioo, abs_lt, exists_prop]

theorem image_subset_nearOrbit {S : Set X} {j : ℤ} (hj : |j| < r) :
    (T ^ j) '' S ⊆ nearOrbit T r S :=
  fun _ hx => (mem_nearOrbit T r).2 ⟨j, hj, hx⟩

theorem nearOrbit_mono {S S' : Set X} (h : S ⊆ S') : nearOrbit T r S ⊆ nearOrbit T r S' := by
  intro x hx
  obtain ⟨j, hj, y, hy, rfl⟩ := (mem_nearOrbit T r).1 hx
  exact image_subset_nearOrbit T r hj ⟨y, h hy, rfl⟩

theorem isClopen_nearOrbit {S : Set X} (hS : IsClopen S) : IsClopen (nearOrbit T r S) :=
  isClopen_biUnion_finset fun j _ => ClopenCrossedProduct.isClopen_image (T ^ j) hS

/-- **The printed recursion** `C_0 = ∅`, `C_{i+1} = C_i ∪ (U_{i+1} \ ⋃_{|j|<r} T^j C_i)`
(tex 1710–1714), with the cover indexed from `0`. -/
def sectionStep (U : ℕ → Set X) : ℕ → Set X
  | 0 => ∅
  | i + 1 => sectionStep U i ∪ (U i \ nearOrbit T r (sectionStep U i))

theorem sectionStep_succ (U : ℕ → Set X) (i : ℕ) :
    sectionStep T r U (i + 1) = sectionStep T r U i ∪ (U i \ nearOrbit T r (sectionStep T r U i)) :=
  rfl

theorem sectionStep_mono (U : ℕ → Set X) : Monotone (sectionStep T r U) :=
  monotone_nat_of_le_succ fun _ => subset_union_left

theorem isClopen_sectionStep {U : ℕ → Set X} (hU : ∀ i, IsClopen (U i)) (i : ℕ) :
    IsClopen (sectionStep T r U i) := by
  induction i with
  | zero => exact isClopen_empty
  | succ i ih => exact ih.union ((hU i).diff (isClopen_nearOrbit T r ih))

/-- **`C_i` is separated from its first `r - 1` translates** (tex 1716). -/
theorem disjoint_sectionStep {U : ℕ → Set X}
    (hU : ∀ i (j : ℕ), 0 < j → j < r → Disjoint (U i) ((T ^ (j : ℤ)) '' U i)) (i : ℕ) :
    ∀ j : ℕ, 0 < j → j < r →
      Disjoint (sectionStep T r U i) ((T ^ (j : ℤ)) '' sectionStep T r U i) := by
  induction i with
  | zero =>
    intro j _ _
    exact empty_disjoint _
  | succ i ih =>
    intro j h₁ h₂
    have hjr : |(j : ℤ)| < r := by
      rw [abs_of_nonneg (Int.natCast_nonneg j)]
      exact_mod_cast h₂
    have hnjr : |-(j : ℤ)| < r := by rwa [abs_neg]
    rw [sectionStep_succ, image_union, disjoint_union_left, disjoint_union_right,
      disjoint_union_right]
    refine ⟨⟨ih j h₁ h₂, ?_⟩, ?_, ?_⟩
    · refine disjoint_left.2 fun y hy hyimg => ?_
      obtain ⟨z, hz, rfl⟩ := hyimg
      exact hz.2 (image_subset_nearOrbit T r hnjr
        ⟨(T ^ (j : ℤ)) z, hy, zpow_neg_apply_zpow_apply_homeomorph T _ z⟩)
    · exact disjoint_left.2 fun y hy hyimg => hy.2 (image_subset_nearOrbit T r hjr hyimg)
    · exact (hU i j h₁ h₂).mono (fun _ h => h.1) (image_mono fun _ h => h.1)

/-- `U_{i+1} ⊆ ⋃_{|j|<r} T^j C_{i+1}` (tex 1717). -/
theorem subset_nearOrbit_sectionStep (hr : 1 ≤ r) (U : ℕ → Set X) (i : ℕ) :
    U i ⊆ nearOrbit T r (sectionStep T r U (i + 1)) := by
  intro y hy
  by_cases hyn : y ∈ nearOrbit T r (sectionStep T r U i)
  · exact nearOrbit_mono T r (sectionStep_mono T r U (Nat.le_succ i)) hyn
  · refine image_subset_nearOrbit T r (j := 0) (by rw [abs_zero]; exact_mod_cast hr)
      ⟨y, ?_, by rw [zpow_zero, Homeomorph.one_apply]⟩
    rw [sectionStep_succ]
    exact Or.inr ⟨hy, hyn⟩

/-- Extend a cover `U : Fin m → Set X` by `∅`. -/
def extendCover {m : ℕ} (U : Fin m → Set X) (i : ℕ) : Set X :=
  if h : i < m then U ⟨i, h⟩ else ∅

variable {T r}

/-- **The section construction** (tex 1709–1717): a return section of spread `r`. -/
theorem exists_isReturnSection [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (hr : 1 ≤ r) (hT : NoShortPeriods T r) : ∃ C : Set X, IsReturnSection T r C := by
  obtain ⟨m, U, hUc, hUcov, hUd⟩ := exists_separated_clopen_cover T hT
  have hVc : ∀ i, IsClopen (extendCover U i) := fun i => by
    by_cases h : i < m
    · rw [extendCover, dif_pos h]
      exact hUc _
    · rw [extendCover, dif_neg h]
      exact isClopen_empty
  have hVd : ∀ i (j : ℕ), 0 < j → j < r →
      Disjoint (extendCover U i) ((T ^ (j : ℤ)) '' extendCover U i) := fun i j h₁ h₂ => by
    by_cases h : i < m
    · rw [extendCover, dif_pos h]
      exact hUd _ j h₁ h₂
    · rw [extendCover, dif_neg h]
      exact empty_disjoint _
  refine ⟨sectionStep T r (extendCover U) m,
    ⟨isClopen_sectionStep T r hVc m, disjoint_sectionStep T r hVd m, fun x => ?_⟩⟩
  obtain ⟨i, hi⟩ := hUcov x
  have hx : x ∈ extendCover U i := by
    rw [extendCover, dif_pos i.2]
    exact hi
  exact (mem_nearOrbit T r).1 (nearOrbit_mono T r
    (sectionStep_mono T r (extendCover U) (Nat.succ_le_of_lt i.2))
    (subset_nearOrbit_sectionStep T r hr (extendCover U) i hx))

end Recursion

/-! ### Return gaps (tex 1717–1719) -/

section ReturnTime

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X}

/-- **Every point visits `C` within `2r - 1` steps**, through the middle point `T^r x`
(tex 1717–1718): `T^r x ∈ T^j C` with `|j| < r` gives `T^{r-j} x ∈ C`, `0 < r - j < 2r`. -/
theorem IsReturnSection.exists_return (hC : IsReturnSection T r C) (x : X) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 * r - 1 ∧ (T ^ (n : ℤ)) x ∈ C := by
  obtain ⟨j, hj, c, hc, hcx⟩ := hC.exists_mem_image ((T ^ (r : ℤ)) x)
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hj
  have hc' : c = (T ^ ((r : ℤ) - j)) x := by
    rw [← zpow_neg_apply_zpow_apply_homeomorph T j c, hcx, zpow_apply_zpow_apply_homeomorph,
      show -j + (r : ℤ) = (r : ℤ) - j by ring]
  refine ⟨((r : ℤ) - j).toNat, by omega, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), ← hc']
  exact hc

theorem IsReturnSection.returns (hC : IsReturnSection T r C) (x : X) :
    ∃ n : ℕ, 0 < n ∧ (T ^ (n : ℤ)) x ∈ C :=
  let ⟨n, h₁, _, h₃⟩ := hC.exists_return x
  ⟨n, h₁, h₃⟩

theorem returnTime_spec (hC : IsReturnSection T r C) (x : X) :
    0 < returnTime T C x ∧ (T ^ (returnTime T C x : ℤ)) x ∈ C := by
  classical
  unfold returnTime
  rw [dif_pos (hC.returns x)]
  exact Nat.find_spec (hC.returns x)

theorem returnTime_min (hC : IsReturnSection T r C) (x : X) {j : ℕ} (h₁ : 0 < j)
    (h₂ : j < returnTime T C x) : (T ^ (j : ℤ)) x ∉ C := by
  classical
  intro hj
  unfold returnTime at h₂
  rw [dif_pos (hC.returns x)] at h₂
  exact Nat.find_min (hC.returns x) h₂ ⟨h₁, hj⟩

theorem returnTime_le_of_mem (hC : IsReturnSection T r C) (x : X) {n : ℕ} (hn : 0 < n)
    (hnC : (T ^ (n : ℤ)) x ∈ C) : returnTime T C x ≤ n := by
  classical
  unfold returnTime
  rw [dif_pos (hC.returns x)]
  exact Nat.find_le ⟨hn, hnC⟩

theorem returnTime_le (hC : IsReturnSection T r C) (x : X) :
    returnTime T C x ≤ 2 * r - 1 := by
  obtain ⟨n, h₁, h₂, h₃⟩ := hC.exists_return x
  exact (returnTime_le_of_mem hC x h₁ h₃).trans h₂

/-- A first visit is the return time. -/
theorem returnTime_eq_of (hC : IsReturnSection T r C) (x : X) {h : ℕ} (hh : 0 < h)
    (hhC : (T ^ (h : ℤ)) x ∈ C) (hmin : ∀ j : ℕ, 0 < j → j < h → (T ^ (j : ℤ)) x ∉ C) :
    returnTime T C x = h := by
  refine le_antisymm (returnTime_le_of_mem hC x hh hhC) (not_lt.1 fun hlt => ?_)
  obtain ⟨h₁, h₃⟩ := returnTime_spec hC x
  exact hmin _ h₁ hlt h₃

/-- The return time is at least `r`: `C` is separated from its first `r - 1` translates. -/
theorem le_returnTime (hC : IsReturnSection T r C) {x : X} (hx : x ∈ C) :
    r ≤ returnTime T C x := by
  by_contra hlt
  obtain ⟨h₁, h₃⟩ := returnTime_spec hC x
  exact disjoint_left.1 (hC.disjoint_image _ h₁ (not_le.1 hlt)) h₃ ⟨x, hx, rfl⟩

/-- **The return gaps lie in `[r, 2r - 1]`** (tex 1717). -/
theorem IsReturnSection.returnGapsIn (hC : IsReturnSection T r C) :
    ReturnGapsIn T C r (2 * r - 1) :=
  fun x hx => ⟨_, le_returnTime hC hx, returnTime_le hC x, (returnTime_spec hC x).2,
    fun _ h₁ h₂ => returnTime_min hC x h₁ h₂⟩

/-- For `r = 1` a return section is all of `X` (tex 1719). -/
theorem IsReturnSection.eq_univ_of_one (hC : IsReturnSection T 1 C) : C = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨j, hj, c, hc, hcx⟩ := hC.exists_mem_image x
  have hj0 : j = 0 := by
    have := abs_lt.1 hj
    omega
  subst hj0
  rw [zpow_zero, Homeomorph.one_apply] at hcx
  exact hcx ▸ hc

/-- **For `r = 1` simply take `C = X`** (tex 1719). -/
theorem isReturnSection_univ_one : IsReturnSection T 1 (univ : Set X) where
  isClopen := isClopen_univ
  disjoint_image _ h₁ h₂ := absurd h₂ (by omega)
  exists_mem_image x := ⟨0, by simp, x, mem_univ x, by rw [zpow_zero, Homeomorph.one_apply]⟩

end ReturnTime

/-- **The section construction of `cor:dynamic-rank-budget`** (tex 1709–1719), closed. -/
theorem returnSectionStatement_holds : ReturnSectionStatement := by
  intro X _ _ _ _ T r hr hT
  obtain ⟨C, hC⟩ := exists_isReturnSection hr hT
  exact ⟨C, hC, hC.returnGapsIn⟩

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_closed_axioms returnSectionStatement_holds
#audit_axioms IsReturnSection.returnGapsIn
#audit_axioms IsReturnSection.eq_univ_of_one
