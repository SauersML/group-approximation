import GroupApproximation.Dynamics.InvolutionLocalizationStatement
import GroupApproximation.Dynamics.TransientSupport
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.NoncommRing

/-!
# `lem:involution-localization`: the finite-field clause

`non_mf_groups_exist.tex`, `\label{lem:involution-localization}` (tex 1663–1667) and its proof
(tex 1672–1687):

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and
> $J=p_CIp_C$.  Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with
> $w-1\in I$, $w^2=1$, and $wFw^{-1}\subset J$.
>
> Let $K\subset X\setminus Y$ contain the sources and ranges of a finite partial-shift description of
> $F$, and cover $K$ by $m$ wandering clopen sets.  Each orbit meets $K$ at most $m$ times.  If $H$
> bounds the return gaps, add arrows from every point of $K$ to its first $2m$ strictly future
> returns to $C$.  [...]  At least $m$ of the latter lie in $C\setminus K$, enough to match every
> original coordinate to a fresh section coordinate.  Swap the matched pairs and fix the other
> coordinates.  The finite clopen partition makes these choices constant on each representative
> cell.  Unitizing the resulting permutations gives an involution $w$ with $w1_Kw^{-1}\le p_C$, hence
> $wFw^{-1}\subset J$.

The proof composes the landed steps:

* `exists_clopen_support` (TransientSupport): `F ⊆ 1_K R_X 1_K` for a clopen `K ⊆ X ∖ Y`;
* `exists_wandering_clopen_cover` (TransientSupport): `m` wandering clopen sets cover `K`, from the
  defect cover of lem:chain-core-models (`ChainCoreDefectCoverStatement`);
* `exists_uniform_return` (TransientSupport): the section is reached within `L` positive steps;
* `Dynamics.exists_returnPlacement` (ReturnPlacement): clopen cells of `K` matched to pairwise
  disjoint fresh coordinates in `C ∖ K` by exponents `0 < h ≤ 2mL`;
* `exists_swapUnit` (ClopenSwapInvolution): the unitized swap `w`, with `w⁻¹ = w` and
  `w 1_A w⁻¹ = 1_{T^h(A)}` on each cell.

Then `w 1_K w⁻¹ = ∑ 1_{T^h(A)} ≤ p_C`, and `w x w⁻¹ = (w 1_K w⁻¹)(w x w⁻¹)(w 1_K w⁻¹)` lies in `J`.

Construction order: the cells come from the piecewise matching of `ReturnPlacement` rather than from
the matrix-block construction of lem:transient-matrices; see that module's docstring.
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

section RingIdentities

variable {R : Type*} [Ring R]

/-- If `e x = x = x e`, then `w x w⁻¹ = (w e w⁻¹)(w x w⁻¹)(w e w⁻¹)`. -/
theorem conj_eq_sandwich (w : Rˣ) {e x : R} (hl : e * x = x) (hr : x * e = x) :
    (w : R) * x * ↑w⁻¹ =
      ((w : R) * e * ↑w⁻¹) * ((w : R) * x * ↑w⁻¹) * ((w : R) * e * ↑w⁻¹) := by
  have h1 : ((w⁻¹ : Rˣ) : R) * w = 1 := Units.inv_mul w
  calc (w : R) * x * ↑w⁻¹ = (w : R) * (e * x * e) * ↑w⁻¹ := by rw [hl, hr]
    _ = (w : R) * e * (↑w⁻¹ * ↑w) * x * (↑w⁻¹ * ↑w) * e * ↑w⁻¹ := by
      rw [h1]
      noncomm_ring
    _ = ((w : R) * e * ↑w⁻¹) * ((w : R) * x * ↑w⁻¹) * ((w : R) * e * ↑w⁻¹) := by noncomm_ring

/-- If `E c = E = c E` and `a = E a E`, then `c a c = a`. -/
theorem sandwich_eq_self {c E a : R} (hEc : E * c = E) (hcE : c * E = E) (ha : a = E * a * E) :
    c * a * c = a := by
  calc c * a * c = c * (E * a * E) * c := by rw [← ha]
    _ = (c * E) * a * (E * c) := by noncomm_ring
    _ = E * a * E := by rw [hcE, hEc]
    _ = a := ha.symm

end RingIdentities

section Partition

variable {X : Type*} [TopologicalSpace X]

theorem locallyConstant_sum_apply {k : Type*} [Ring k] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → LocallyConstant X k) (y : X) : (∑ i ∈ s, f i) y = ∑ i ∈ s, f i y := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, LocallyConstant.zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, LocallyConstant.add_apply, ih]

/-- `1_K = ∑ 1_{B p}` when the clopen sets `B p`, `p ∈ N`, partition `K`. -/
theorem charFn_eq_sum_of_partition (k : Type*) [Ring k] {ι : Type*} [DecidableEq ι]
    (N : Finset ι) {K : Set X} (hK : IsClopen K) (B : ι → Set X) (hB : ∀ p, IsClopen (B p))
    (hsub : ∀ p ∈ N, B p ⊆ K) (hdisj : ∀ p ∈ N, ∀ q ∈ N, p ≠ q → Disjoint (B p) (B q))
    (hcov : ∀ y ∈ K, ∃ p ∈ N, y ∈ B p) :
    LocallyConstant.charFn k hK = ∑ p ∈ N, LocallyConstant.charFn k (hB p) := by
  ext y
  rw [locallyConstant_sum_apply]
  simp only [LocallyConstant.coe_charFn]
  by_cases hy : y ∈ K
  · obtain ⟨p, hp, hyp⟩ := hcov y hy
    rw [Set.indicator_of_mem hy, Finset.sum_eq_single_of_mem p hp fun q hq hqp => ?_,
      Set.indicator_of_mem hyp]
    exact Set.indicator_of_notMem
      (fun hyq => Set.disjoint_left.1 (hdisj q hq p hp hqp) hyq hyp) _
  · rw [Set.indicator_of_notMem hy]
    exact (Finset.sum_eq_zero fun q hq =>
      Set.indicator_of_notMem (fun hyq => hy (hsub q hq hyq)) _).symm

end Partition

section Core

/-- `Y = CR(T)` is invariant under every integer power of `T`. -/
theorem zpow_mem_chainRecurrentSet {X : Type*} [UniformSpace X] [CompactSpace X] (T : X ≃ₜ X)
    (j : ℤ) :
    ∀ y ∈ Dynamics.chainRecurrentSet ⇑T, (T ^ j) y ∈ Dynamics.chainRecurrentSet ⇑T := by
  induction j using Int.induction_on with
  | zero =>
    intro y hy
    rwa [zpow_zero, Homeomorph.one_apply]
  | succ i ih =>
    intro y hy
    rw [zpow_add_one, Homeomorph.mul_apply]
    exact ih _ ((Dynamics.apply_mem_chainRecurrentSet_iff T).2 hy)
  | pred i ih =>
    intro y hy
    rw [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply]
    exact ih _ ((Dynamics.apply_mem_chainRecurrentSet_iff T).1 (by rwa [Homeomorph.apply_symm_apply]))

/-- `x ∈ I` iff every Laurent coefficient of `x` vanishes on `Y = CR(T)`. -/
theorem mem_coreTransientIdeal_iff {X : Type} [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X)
    (k : Type) [Ring k] (x : ClopenCrossedProduct T k) :
    x ∈ coreTransientIdeal T k ↔ CoeffVanishOn T k (Dynamics.chainRecurrentSet ⇑T) x :=
  mem_transientIdeal_iff_forall_coeff T k (Dynamics.image_chainRecurrentSet T)

end Core

/-- **lem:involution-localization, finite-field clause** (tex 1664–1667), along the printed proof
(tex 1672–1687), over the defect cover of lem:chain-core-models. -/
theorem involutionLocalizationRingClause_of_cover (hcover : ChainCoreDefectCoverStatement) :
    InvolutionLocalizationRingClause := by
  intro X _ _ _ _ T C hC hfull hbound k _ _ F hF
  classical
  have hYinv : ∀ j : ℤ, ∀ y ∈ Dynamics.chainRecurrentSet ⇑T,
      (T ^ j) y ∈ Dynamics.chainRecurrentSet ⇑T := fun j => zpow_mem_chainRecurrentSet T j
  obtain ⟨K, hK, hKY, hKF⟩ := exists_clopen_support T k hYinv F
    fun x hx => (mem_coreTransientIdeal_iff T k x).1 (hF x hx)
  obtain ⟨m, W, hWc, hWw, hKW⟩ := exists_wandering_clopen_cover T (hcover X T) hK hKY
  obtain ⟨H, hH⟩ := hbound
  obtain ⟨L, hL⟩ := exists_uniform_return hC hfull hH
  obtain ⟨A, hA⟩ := Dynamics.exists_returnPlacement T W K C L hK hC hWc hWw hKW hL
  obtain ⟨N, hN⟩ : ∃ N : Finset (Fin m × ℕ),
      N = Finset.univ ×ˢ Finset.range (2 * m * L + 1) := ⟨_, rfl⟩
  have hBc : ∀ p : Fin m × ℕ, IsClopen (A p.1 p.2) := fun p => hA.isClopen p.1 p.2
  have hmemN : ∀ p : Fin m × ℕ, (A p.1 p.2).Nonempty → p ∈ N := fun p hp => by
    have hle := (hA.bounds p.1 p.2 hp).2.2
    rw [hN]
    exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_range.2 (by omega)⟩
  have hsubC : ∀ p : Fin m × ℕ, ⇑(T ^ (p.2 : ℤ)) '' A p.1 p.2 ⊆ C :=
    fun p _ hy => (hA.target p.1 p.2 hy).1
  obtain ⟨w, hwinv, hwconj, hwdev⟩ := exists_swapUnit T k N (fun p => A p.1 p.2) hBc
    (fun p => (p.2 : ℤ)) (fun p _ q _ hpq => hA.disjoint_source hpq)
    (fun p _ q _ hpq => hA.disjoint_target p.1 p.2 q.1 q.2 hpq)
    (fun p _ q _ => Set.disjoint_left.2 fun y hy hy' =>
      (hA.target q.1 q.2 hy').2 (hA.subset_K p.1 p.2 hy))
  refine ⟨w, ?_, ?_, fun x hx => ?_⟩
  · -- `w - 1 ∈ I`: the deviation is a combination of partial shifts supported off `Y`.
    rw [hwdev]
    refine Finset.sum_induction _ (· ∈ coreTransientIdeal T k)
      (fun _ _ ha hb => (coreTransientIdeal T k).add_mem ha hb)
      (coreTransientIdeal T k).zero_mem fun p _ => ?_
    have hBY : Disjoint (A p.1 p.2) (Dynamics.chainRecurrentSet ⇑T) :=
      hKY.mono_left (hA.subset_K p.1 p.2)
    have hTBY : Disjoint (⇑(T ^ (p.2 : ℤ)) '' A p.1 p.2) (Dynamics.chainRecurrentSet ⇑T) := by
      rw [Set.disjoint_left]
      rintro _ ⟨b, hb, rfl⟩ hbY
      refine Set.disjoint_left.1 hBY hb ?_
      have hback := hYinv (-(p.2 : ℤ)) _ hbY
      rwa [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero,
        Homeomorph.one_apply] at hback
    have h1 : coeff T k (LocallyConstant.charFn k (hBc p)) ∈ coreTransientIdeal T k :=
      (mem_coreTransientIdeal_iff T k _).2 (coeffVanishOn_charFn (hBc p) hBY)
    have h2 : coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))) ∈
        coreTransientIdeal T k :=
      (mem_coreTransientIdeal_iff T k _).2
        (coeffVanishOn_charFn (isClopen_image (T ^ (p.2 : ℤ)) (hBc p)) hTBY)
    exact (coreTransientIdeal T k).sub_mem ((coreTransientIdeal T k).sub_mem
      ((coreTransientIdeal T k).add_mem ((coreTransientIdeal T k).mul_mem_left _ _ h1)
        ((coreTransientIdeal T k).mul_mem_right _ _ h1)) h1) h2
  · -- `w² = 1`.
    calc (w : ClopenCrossedProduct T k) * w = w * ↑w⁻¹ := by rw [hwinv]
      _ = 1 := Units.mul_inv w
  · -- `w x w⁻¹ ∈ J`.
    obtain ⟨hxl, hxr⟩ := hKF x hx
    refine ⟨(w : ClopenCrossedProduct T k) * x * ↑w⁻¹,
      (coreTransientIdeal T k).mul_mem_right _ _
        ((coreTransientIdeal T k).mul_mem_left _ _ (hF x hx)), ?_⟩
    have hKsum := charFn_eq_sum_of_partition k N hK (fun p => A p.1 p.2) hBc
      (fun p _ => hA.subset_K p.1 p.2) (fun p _ q _ hpq => hA.disjoint_source hpq)
      (fun y hy => by
        obtain ⟨j, g, hyg⟩ := hA.exists_mem hKW hy
        exact ⟨(j, g), hmemN (j, g) ⟨y, hyg⟩, hyg⟩)
    have hE : (w : ClopenCrossedProduct T k) * coeff T k (LocallyConstant.charFn k hK) * ↑w⁻¹ =
        ∑ p ∈ N, coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))) := by
      rw [hKsum, map_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p hp => hwconj p hp
    have hEc : (∑ p ∈ N, coeff T k
          (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p)))) *
        coeff T k (LocallyConstant.charFn k hC) =
        ∑ p ∈ N, coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by
        rw [← map_mul, charFn_mul_charFn_of_subset k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p)) hC
          (hsubC p)]
    have hcE : coeff T k (LocallyConstant.charFn k hC) *
        ∑ p ∈ N, coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))) =
        ∑ p ∈ N, coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by
        rw [← map_mul, charFn_mul_charFn_of_superset k hC (isClopen_image (T ^ (p.2 : ℤ)) (hBc p))
          (hsubC p)]
    have hsand := conj_eq_sandwich w hxl hxr
    rw [hE] at hsand
    exact (sandwich_eq_self hEc hcE hsand).symm

end ClopenCrossedProduct

end GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.zpow_mem_chainRecurrentSet
#audit_axioms GroupApproximation.ClopenCrossedProduct.charFn_eq_sum_of_partition
#audit_axioms GroupApproximation.ClopenCrossedProduct.involutionLocalizationRingClause_of_cover
