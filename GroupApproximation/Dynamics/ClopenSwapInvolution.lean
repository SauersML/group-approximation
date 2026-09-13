import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.NoncommRing

/-!
# The swap involution of `lem:involution-localization`

`non_mf_groups_exist.tex`, proof of `lem:involution-localization` (tex 1684–1687):

> Swap the matched pairs and fix the other coordinates.  The finite clopen partition makes these
> choices constant on each representative cell.  Unitizing the resulting permutations gives an
> involution $w$ with $w1_Kw^{-1}\le p_C$, hence $wFw^{-1}\subset J$.

A matched pair is a clopen set `A` of original coordinates together with an exponent `h`; its fresh
coordinates are `T^h(A)`.  The partial shift `s = u^h 1_A` moves `A` onto `T^h(A)` and
`t = 1_A u^{-h}` moves it back.  Unitizing a finite family of pairwise disjoint pairs gives

  `w = 1 - ∑ᵢ (1_{Aᵢ} + 1_{T^{hᵢ}(Aᵢ)}) + ∑ᵢ (sᵢ + tᵢ)`.

* `IsSwapFamily`: the relations of such a family in an arbitrary ring, with
  `IsSwapFamily.swapElement_mul_self : w * w = 1` and
  `IsSwapFamily.swapElement_mul_mul_swapElement : w * eᵢ * w = fᵢ`;
* `unit_zpow_mul_charFn : u^h 1_A = 1_{T^h(A)} u^h` in `R_X`;
* `isSwapFamily_clopen`: pairwise disjoint clopen pairs form a swap family in `R_X`;
* `exists_swapUnit`: the unitized involution `w`, with `w⁻¹ = w`,
  `w 1_{Aᵢ} w⁻¹ = 1_{T^{hᵢ}(Aᵢ)}` and `w - 1 = ∑ᵢ (sᵢ + tᵢ - 1_{Aᵢ} - 1_{T^{hᵢ}(Aᵢ)})`.
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

section SwapFamily

variable {S : Type*} [Ring S]

/-- `(1 - E + v)² = 1` when `E² = E`, `E v = v = v E` and `v² = E`. -/
theorem one_sub_add_mul_self_eq_one {E v : S} (hE : E * E = E) (hEv : E * v = v)
    (hvE : v * E = v) (hv : v * v = E) : (1 - E + v) * (1 - E + v) = 1 := by
  have e : (1 - E + v) * (1 - E + v) - 1 =
      (E * E - E) - (E * v - v) - (v * E - v) + (v * v - E) := by
    noncomm_ring
  rw [← sub_eq_zero, e, sub_eq_zero.2 hE, sub_eq_zero.2 hEv, sub_eq_zero.2 hvE,
    sub_eq_zero.2 hv]
  simp

variable {ι : Type*}

/-- The relations of a finite family of matched pairs in a ring: pairwise orthogonal idempotents
`e i` (original coordinates) and `f i` (fresh coordinates), with partial isometries `s i` from
`e i` to `f i` and `t i` back. -/
structure IsSwapFamily (N : Finset ι) (e f s t : ι → S) : Prop where
  e_mul_e : ∀ i ∈ N, e i * e i = e i
  f_mul_f : ∀ i ∈ N, f i * f i = f i
  e_mul_e_of_ne : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → e i * e j = 0
  f_mul_f_of_ne : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → f i * f j = 0
  e_mul_f : ∀ i ∈ N, ∀ j ∈ N, e i * f j = 0
  f_mul_e : ∀ i ∈ N, ∀ j ∈ N, f i * e j = 0
  s_mul_t : ∀ i ∈ N, s i * t i = f i
  t_mul_s : ∀ i ∈ N, t i * s i = e i
  f_mul_s : ∀ i ∈ N, f i * s i = s i
  s_mul_e : ∀ i ∈ N, s i * e i = s i
  e_mul_t : ∀ i ∈ N, e i * t i = t i
  t_mul_f : ∀ i ∈ N, t i * f i = t i

namespace IsSwapFamily

variable {N : Finset ι} {e f s t : ι → S} (h : IsSwapFamily N e f s t)
include h

theorem e_mul_s {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : e i * s j = 0 := by
  rw [← h.f_mul_s j hj, ← mul_assoc, h.e_mul_f i hi j hj, zero_mul]

theorem f_mul_s_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : f i * s j = 0 := by
  rw [← h.f_mul_s j hj, ← mul_assoc, h.f_mul_f_of_ne i hi j hj hij, zero_mul]

theorem e_mul_t_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : e i * t j = 0 := by
  rw [← h.e_mul_t j hj, ← mul_assoc, h.e_mul_e_of_ne i hi j hj hij, zero_mul]

theorem f_mul_t {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : f i * t j = 0 := by
  rw [← h.e_mul_t j hj, ← mul_assoc, h.f_mul_e i hi j hj, zero_mul]

theorem s_mul_e_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : s i * e j = 0 := by
  rw [← h.s_mul_e i hi, mul_assoc, h.e_mul_e_of_ne i hi j hj hij, mul_zero]

theorem s_mul_f {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : s i * f j = 0 := by
  rw [← h.s_mul_e i hi, mul_assoc, h.e_mul_f i hi j hj, mul_zero]

theorem t_mul_e {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : t i * e j = 0 := by
  rw [← h.t_mul_f i hi, mul_assoc, h.f_mul_e i hi j hj, mul_zero]

theorem t_mul_f_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : t i * f j = 0 := by
  rw [← h.t_mul_f i hi, mul_assoc, h.f_mul_f_of_ne i hi j hj hij, mul_zero]

theorem s_mul_s {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : s i * s j = 0 := by
  rw [← h.s_mul_e i hi, mul_assoc, h.e_mul_s hi hj, mul_zero]

theorem t_mul_t {i j : ι} (hi : i ∈ N) (hj : j ∈ N) : t i * t j = 0 := by
  rw [← h.t_mul_f i hi, mul_assoc, h.f_mul_t hi hj, mul_zero]

theorem s_mul_t_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : s i * t j = 0 := by
  rw [← h.s_mul_e i hi, mul_assoc, h.e_mul_t_of_ne hi hj hij, mul_zero]

theorem t_mul_s_of_ne {i j : ι} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j) : t i * s j = 0 := by
  rw [← h.t_mul_f i hi, mul_assoc, h.f_mul_s_of_ne hi hj hij, mul_zero]

/-- `E * E = E` for `E = ∑ (e i + f i)`. -/
theorem sumEF_mul_sumEF :
    (∑ i ∈ N, (e i + f i)) * ∑ i ∈ N, (e i + f i) = ∑ i ∈ N, (e i + f i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, mul_add, mul_add, h.e_mul_e_of_ne i hi j hj (Ne.symm hji), h.e_mul_f i hi j hj,
      h.f_mul_e i hi j hj, h.f_mul_f_of_ne i hi j hj (Ne.symm hji)]
    simp only [add_zero]]
  rw [add_mul, mul_add, mul_add, h.e_mul_e i hi, h.e_mul_f i hi i hi, h.f_mul_e i hi i hi,
    h.f_mul_f i hi]
  simp only [add_zero, zero_add]

/-- `E * v = v` for `E = ∑ (e i + f i)` and `v = ∑ (s i + t i)`. -/
theorem sumEF_mul_sumST :
    (∑ i ∈ N, (e i + f i)) * ∑ i ∈ N, (s i + t i) = ∑ i ∈ N, (s i + t i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, mul_add, mul_add, h.e_mul_s hi hj, h.e_mul_t_of_ne hi hj (Ne.symm hji),
      h.f_mul_s_of_ne hi hj (Ne.symm hji), h.f_mul_t hi hj]
    simp only [add_zero]]
  rw [add_mul, mul_add, mul_add, h.e_mul_s hi hi, h.e_mul_t i hi, h.f_mul_s i hi, h.f_mul_t hi hi]
  simp only [add_zero, zero_add]
  exact add_comm _ _

/-- `v * E = v`. -/
theorem sumST_mul_sumEF :
    (∑ i ∈ N, (s i + t i)) * ∑ i ∈ N, (e i + f i) = ∑ i ∈ N, (s i + t i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, mul_add, mul_add, h.s_mul_e_of_ne hi hj (Ne.symm hji), h.s_mul_f hi hj,
      h.t_mul_e hi hj, h.t_mul_f_of_ne hi hj (Ne.symm hji)]
    simp only [add_zero]]
  rw [add_mul, mul_add, mul_add, h.s_mul_e i hi, h.s_mul_f hi hi, h.t_mul_e hi hi, h.t_mul_f i hi]
  simp only [add_zero, zero_add]

/-- `v * v = E`. -/
theorem sumST_mul_sumST :
    (∑ i ∈ N, (s i + t i)) * ∑ i ∈ N, (s i + t i) = ∑ i ∈ N, (e i + f i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, mul_add, mul_add, h.s_mul_s hi hj, h.s_mul_t_of_ne hi hj (Ne.symm hji),
      h.t_mul_s_of_ne hi hj (Ne.symm hji), h.t_mul_t hi hj]
    simp only [add_zero]]
  rw [add_mul, mul_add, mul_add, h.s_mul_s hi hi, h.s_mul_t i hi, h.t_mul_s i hi, h.t_mul_t hi hi]
  simp only [add_zero, zero_add]
  exact add_comm _ _

/-- **The swap is an involution:** `w * w = 1` for `w = 1 - ∑ (e i + f i) + ∑ (s i + t i)`. -/
theorem swapElement_mul_self :
    (1 - ∑ i ∈ N, (e i + f i) + ∑ i ∈ N, (s i + t i)) *
      (1 - ∑ i ∈ N, (e i + f i) + ∑ i ∈ N, (s i + t i)) = 1 :=
  one_sub_add_mul_self_eq_one h.sumEF_mul_sumEF h.sumEF_mul_sumST h.sumST_mul_sumEF
    h.sumST_mul_sumST

theorem sumEF_mul_e {i : ι} (hi : i ∈ N) : (∑ j ∈ N, (e j + f j)) * e i = e i := by
  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, h.e_mul_e_of_ne j hj i hi hji, h.f_mul_e j hj i hi, add_zero]]
  rw [add_mul, h.e_mul_e i hi, h.f_mul_e i hi i hi, add_zero]

theorem sumST_mul_e {i : ι} (hi : i ∈ N) : (∑ j ∈ N, (s j + t j)) * e i = s i := by
  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [add_mul, h.s_mul_e_of_ne hj hi hji, h.t_mul_e hj hi, add_zero]]
  rw [add_mul, h.s_mul_e i hi, h.t_mul_e hi hi, add_zero]

theorem s_mul_sumEF {i : ι} (hi : i ∈ N) : s i * ∑ j ∈ N, (e j + f j) = s i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [mul_add, h.s_mul_e_of_ne hi hj (Ne.symm hji), h.s_mul_f hi hj, add_zero]]
  rw [mul_add, h.s_mul_e i hi, h.s_mul_f hi hi, add_zero]

theorem s_mul_sumST {i : ι} (hi : i ∈ N) : s i * ∑ j ∈ N, (s j + t j) = f i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi fun j hj hji => by
    rw [mul_add, h.s_mul_s hi hj, h.s_mul_t_of_ne hi hj (Ne.symm hji), add_zero]]
  rw [mul_add, h.s_mul_s hi hi, h.s_mul_t i hi, zero_add]

/-- **The swap moves each original coordinate onto its fresh coordinate:** `w * e i * w = f i`. -/
theorem swapElement_mul_mul_swapElement {i : ι} (hi : i ∈ N) :
    (1 - ∑ j ∈ N, (e j + f j) + ∑ j ∈ N, (s j + t j)) * e i *
      (1 - ∑ j ∈ N, (e j + f j) + ∑ j ∈ N, (s j + t j)) = f i := by
  have h1 : (1 - ∑ j ∈ N, (e j + f j) + ∑ j ∈ N, (s j + t j)) * e i = s i := by
    rw [add_mul, sub_mul, one_mul, h.sumEF_mul_e hi, h.sumST_mul_e hi, sub_self, zero_add]
  rw [h1, mul_add, mul_sub, mul_one, h.s_mul_sumEF hi, h.s_mul_sumST hi, sub_self, zero_add]

end IsSwapFamily

/-- `w - 1 = ∑ (s i + t i - e i - f i)` for `w = 1 - ∑ (e i + f i) + ∑ (s i + t i)`. -/
theorem swapElement_sub_one (N : Finset ι) (e f s t : ι → S) :
    (1 - ∑ i ∈ N, (e i + f i) + ∑ i ∈ N, (s i + t i)) - 1 =
      ∑ i ∈ N, (s i + t i - e i - f i) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel

section Pair

variable {U V e f : S}

/-- `u e u⁻¹ = f` in the form `U * e * V = f`. -/
theorem conj_eq_of_mul_eq (hUV : U * V = 1) (hUe : U * e = f * U) : U * e * V = f := by
  rw [hUe, mul_assoc, hUV, mul_one]

theorem pair_f_mul_f (hUV : U * V = 1) (hVU : V * U = 1) (he : e * e = e) (hUe : U * e = f * U) :
    f * f = f := by
  rw [← conj_eq_of_mul_eq hUV hUe]
  calc U * e * V * (U * e * V) = U * e * (V * U) * e * V := by noncomm_ring
    _ = U * e * V := by rw [hVU, mul_one, mul_assoc U e e, he]

theorem pair_s_mul_t (hUV : U * V = 1) (he : e * e = e) (hUe : U * e = f * U) :
    U * e * (e * V) = f := by
  calc U * e * (e * V) = U * (e * e) * V := by noncomm_ring
    _ = f := by rw [he, conj_eq_of_mul_eq hUV hUe]

theorem pair_t_mul_s (hVU : V * U = 1) (he : e * e = e) : e * V * (U * e) = e := by
  calc e * V * (U * e) = e * (V * U) * e := by noncomm_ring
    _ = e := by rw [hVU, mul_one, he]

theorem pair_f_mul_s (he : e * e = e) (hUe : U * e = f * U) : f * (U * e) = U * e := by
  rw [← mul_assoc, ← hUe, mul_assoc, he]

theorem pair_s_mul_e (he : e * e = e) : U * e * e = U * e := by
  rw [mul_assoc, he]

theorem pair_e_mul_t (he : e * e = e) : e * (e * V) = e * V := by
  rw [← mul_assoc, he]

theorem pair_t_mul_f (hUV : U * V = 1) (hVU : V * U = 1) (he : e * e = e) (hUe : U * e = f * U) :
    e * V * f = e * V := by
  rw [← conj_eq_of_mul_eq hUV hUe]
  calc e * V * (U * e * V) = e * (V * U) * e * V := by noncomm_ring
    _ = e * V := by rw [hVU, mul_one, he]

end Pair

end SwapFamily

section Clopen

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k]

theorem image_zpow_eq_preimage_neg (j : ℤ) (A : Set X) :
    ⇑(T ^ j) '' A = ⇑(T ^ (-j)) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    show (T ^ (-j)) ((T ^ j) a) ∈ A
    rwa [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  · intro hx
    refine ⟨(T ^ (-j)) x, hx, ?_⟩
    rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]

theorem charFn_mul_charFn_of_disjoint {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (h : Disjoint U V) :
    LocallyConstant.charFn k hU * LocallyConstant.charFn k hV = 0 := by
  ext x
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn, LocallyConstant.zero_apply]
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_notMem (Set.disjoint_left.1 h hx), mul_zero]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

/-- `1_A ∘ T^{-j} = 1_{T^j(A)}`. -/
theorem comap_zpow_charFn (j : ℤ) {A : Set X} (hA : IsClopen A) :
    LocallyConstant.comap ⟨⇑(T ^ (-j)), (T ^ (-j)).continuous⟩ (LocallyConstant.charFn k hA) =
      LocallyConstant.charFn k (isClopen_image (T ^ j) hA) := by
  have hmem : ∀ x, x ∈ ⇑(T ^ j) '' A ↔ (T ^ (-j)) x ∈ A := fun x => by
    rw [image_zpow_eq_preimage_neg, Set.mem_preimage]
  ext x
  rw [LocallyConstant.coe_comap_apply]
  simp only [LocallyConstant.coe_charFn, ContinuousMap.coe_mk]
  by_cases hx : (T ^ (-j)) x ∈ A
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).2 hx), Pi.one_apply]
  · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).1 hx)]

/-- `u^j 1_A = 1_{T^j(A)} u^j`. -/
theorem unit_zpow_mul_charFn (j : ℤ) {A : Set X} (hA : IsClopen A) :
    ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        coeff T k (LocallyConstant.charFn k hA) =
      coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ j) hA)) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  have h := Pestov91.CrossedProduct.unit_zpow_mul_C (A := ClopenCoeff T k) j
    (ClopenCoeff.of T k (LocallyConstant.charFn k hA))
  rw [ClopenCoeff.smul_of, comap_zpow_charFn] at h
  exact h

variable {ι : Type*}

/-- Pairwise disjoint clopen matched pairs `(Aᵢ, T^{hᵢ}(Aᵢ))` form a swap family in `R_X`, with
`eᵢ = 1_{Aᵢ}`, `fᵢ = 1_{T^{hᵢ}(Aᵢ)}`, `sᵢ = u^{hᵢ} 1_{Aᵢ}` and `tᵢ = 1_{Aᵢ} u^{-hᵢ}`. -/
theorem isSwapFamily_clopen (N : Finset ι) (A : ι → Set X) (hA : ∀ i, IsClopen (A i))
    (h : ι → ℤ) (hAA : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (A i) (A j))
    (hBB : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (⇑(T ^ h i) '' A i) (⇑(T ^ h j) '' A j))
    (hAB : ∀ i ∈ N, ∀ j ∈ N, Disjoint (A i) (⇑(T ^ h j) '' A j)) :
    IsSwapFamily N (fun i => coeff T k (LocallyConstant.charFn k (hA i)))
      (fun i => coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ h i) (hA i))))
      (fun i => ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        coeff T k (LocallyConstant.charFn k (hA i)))
      (fun i => coeff T k (LocallyConstant.charFn k (hA i)) *
        ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ)⁻¹ : (ClopenCrossedProduct T k)ˣ)) := by
  have idem : ∀ {U : Set X} (hU : IsClopen U),
      coeff T k (LocallyConstant.charFn k hU) * coeff T k (LocallyConstant.charFn k hU) =
        coeff T k (LocallyConstant.charFn k hU) := fun hU => by
    rw [← map_mul, charFn_mul_charFn_of_subset k hU hU subset_rfl]
  have ortho : ∀ {U V : Set X} (hU : IsClopen U) (hV : IsClopen V), Disjoint U V →
      coeff T k (LocallyConstant.charFn k hU) * coeff T k (LocallyConstant.charFn k hV) = 0 :=
    fun hU hV hUV => by rw [← map_mul, charFn_mul_charFn_of_disjoint k hU hV hUV, map_zero]
  have hUV : ∀ i, ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
      ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ)⁻¹ : (ClopenCrossedProduct T k)ˣ) = 1 :=
    fun i => Units.mul_inv _
  have hVU : ∀ i, (((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ)⁻¹ :
      (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) = 1 :=
    fun i => Units.inv_mul _
  have hUe := fun i => unit_zpow_mul_charFn T k (h i) (hA i)
  exact
    { e_mul_e := fun i _ => idem (hA i)
      f_mul_f := fun i _ => idem (isClopen_image (T ^ h i) (hA i))
      e_mul_e_of_ne := fun i hi j hj hij => ortho (hA i) (hA j) (hAA i hi j hj hij)
      f_mul_f_of_ne := fun i hi j hj hij => ortho _ _ (hBB i hi j hj hij)
      e_mul_f := fun i hi j hj => ortho _ _ (hAB i hi j hj)
      f_mul_e := fun i hi j hj => ortho _ _ (hAB j hj i hi).symm
      s_mul_t := fun i _ => pair_s_mul_t (hUV i) (idem (hA i)) (hUe i)
      t_mul_s := fun i _ => pair_t_mul_s (hVU i) (idem (hA i))
      f_mul_s := fun i _ => pair_f_mul_s (idem (hA i)) (hUe i)
      s_mul_e := fun i _ => pair_s_mul_e (idem (hA i))
      e_mul_t := fun i _ => pair_e_mul_t (idem (hA i))
      t_mul_f := fun i _ => pair_t_mul_f (hUV i) (hVU i) (idem (hA i)) (hUe i) }

/-- **The unitized swap** (tex 1684–1687): for pairwise disjoint clopen matched pairs
`(Aᵢ, T^{hᵢ}(Aᵢ))` there is a unit `w` of `R_X` with `w⁻¹ = w`, conjugating each `1_{Aᵢ}` onto
`1_{T^{hᵢ}(Aᵢ)}`, and whose deviation `w - 1` is the finite combination of the partial shifts
of the pairs and their indicators. -/
theorem exists_swapUnit (N : Finset ι) (A : ι → Set X) (hA : ∀ i, IsClopen (A i)) (h : ι → ℤ)
    (hAA : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (A i) (A j))
    (hBB : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (⇑(T ^ h i) '' A i) (⇑(T ^ h j) '' A j))
    (hAB : ∀ i ∈ N, ∀ j ∈ N, Disjoint (A i) (⇑(T ^ h j) '' A j)) :
    ∃ w : (ClopenCrossedProduct T k)ˣ,
      ((w⁻¹ : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) = w ∧
      (∀ i ∈ N, (w : ClopenCrossedProduct T k) * coeff T k (LocallyConstant.charFn k (hA i)) *
          ((w⁻¹ : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) =
        coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ h i) (hA i)))) ∧
      (w : ClopenCrossedProduct T k) - 1 =
        ∑ i ∈ N, (((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
            coeff T k (LocallyConstant.charFn k (hA i)) +
          coeff T k (LocallyConstant.charFn k (hA i)) *
            ((unit T k ^ h i : (ClopenCrossedProduct T k)ˣ)⁻¹ : (ClopenCrossedProduct T k)ˣ) -
          coeff T k (LocallyConstant.charFn k (hA i)) -
          coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ h i) (hA i)))) := by
  have hfam := isSwapFamily_clopen T k N A hA h hAA hBB hAB
  refine ⟨⟨_, _, hfam.swapElement_mul_self, hfam.swapElement_mul_self⟩, rfl,
    fun i hi => hfam.swapElement_mul_mul_swapElement hi, ?_⟩
  exact swapElement_sub_one N _ _ _ _

end Clopen

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.IsSwapFamily.swapElement_mul_self
#audit_axioms GroupApproximation.ClopenCrossedProduct.IsSwapFamily.swapElement_mul_mul_swapElement
#audit_axioms GroupApproximation.ClopenCrossedProduct.unit_zpow_mul_charFn
#audit_axioms GroupApproximation.ClopenCrossedProduct.exists_swapUnit
