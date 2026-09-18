import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingLaurent
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingSimpleCentre
import GroupApproximation.Meta.AxiomGuard
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Int.Interval

/-!
# Pair dependence in `LC(X, k) ⋊_T ℤ`: a dimension count on a tower over one cylinder

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315: "for any $p,q$ in it there are $r,r'$,
not both $0$, with $pr+qr'=0$, by a dimension count on a tower over one small cylinder."

For every nonempty topological space `X`, homeomorphism `T` and field `k`, any two elements `p, q`
of `R = LC(X, k) ⋊_T ℤ` have `(r, s) ≠ 0` with `pr + qs = 0` (`exists_pair_dependence`).  The route
is the printed count:

* write `p = ∑_{j ∈ S_p} f_j u^j` and `q = ∑_{j ∈ S_q} g_j u^j` with `|j| ≤ w`;
* choose a clopen `U ∋ x₀` on which every `f_j ∘ T^n` and `g_j ∘ T^n`, `-w ≤ n ≤ 3w`, is constant
  (`exists_clopen_const`);
* the tower `τ_m = u^m e_U = e_{T^m U} u^m` (`towerElem`) satisfies `p τ_m = ∑_{-w ≤ n ≤ 3w} P_{nm} τ_n`
  with scalars `P_{nm}` for `0 ≤ m ≤ 2w` (`mul_towerElem_eq_sum`);
* the `2(2w+1)` columns of `P` and `Q` lie in `k^{4w+1}`, so there is a nontrivial relation
  (`exists_nontrivial_relation`), and `r = ∑ ρ_m τ_m`, `s = ∑ σ_m τ_m` give `pr + qs = 0`
  (`mul_sum_scal_mul_towerElem`);
* the coefficient of `u^m` in `r`, evaluated at `T^m x₀`, is `ρ_m` (`coeff_sum_scal_mul_towerElem`),
  so `r ≠ 0` or `s ≠ 0`.

Adapted (lane-owned copy) from the never-wired orphan
`GroupApproximation/Dynamics/ClopenCrossedProductPairDependence.lean`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui

open ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Field k]

/-- The scalars `k → R`, `c ↦ c · 1`. -/
noncomputable def scal : k →+* ClopenCrossedProduct T k :=
  (coeff T k).comp LocallyConstant.constRingHom

theorem scal_apply (c : k) : scal T k c = coeff T k (LocallyConstant.const X c) :=
  rfl

/-- The tower element `u^m e_U = e_{T^m U} u^m`. -/
noncomputable def towerElem {U : Set X} (hU : IsClopen U) (m : ℤ) : ClopenCrossedProduct T k :=
  coeff T k (LocallyConstant.comap ⟨⇑(T ^ (-m)), (T ^ (-m)).continuous⟩
      (LocallyConstant.charFn k hU)) *
    ((unit T k ^ m : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

/-- One monomial of `p` times one tower element, when the coefficient is constant on `T^{j+m} U`. -/
theorem coeff_mul_unit_zpow_mul_towerElem {U : Set X} (hU : IsClopen U) {x₀ : X}
    (f : LocallyConstant X k) (j m : ℤ)
    (hf : ∀ z ∈ U, f ((T ^ (j + m)) z) = f ((T ^ (j + m)) x₀)) :
    coeff T k f * ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        towerElem T k hU m =
      scal T k (f ((T ^ (j + m)) x₀)) * towerElem T k hU (j + m) := by
  rw [towerElem, towerElem, SimpleKazhdanSofic.coeff_mul_unit_zpow_mul_coeff_mul_unit_zpow, scal_apply, ← mul_assoc,
    ← map_mul]
  congr 2
  ext y
  have hz : (T ^ (-m)) ((T ^ (-j)) y) = (T ^ (-(j + m))) y := by
    rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_rev]
  have hy : (T ^ (j + m)) ((T ^ (-(j + m))) y) = y := by
    rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]
  rw [LocallyConstant.mul_apply, LocallyConstant.mul_apply, LocallyConstant.coe_comap_apply,
    LocallyConstant.coe_comap_apply, LocallyConstant.coe_comap_apply]
  show f y * (LocallyConstant.charFn k hU) ((T ^ (-m)) ((T ^ (-j)) y)) =
    LocallyConstant.const X (f ((T ^ (j + m)) x₀)) y *
      (LocallyConstant.charFn k hU) ((T ^ (-(j + m))) y)
  rw [hz]
  by_cases hU' : (T ^ (-(j + m))) y ∈ U
  · rw [(LocallyConstant.charFn_eq_one k _ hU).mpr hU', mul_one, mul_one, LocallyConstant.coe_const,
      Function.const_apply, ← hf _ hU', hy]
  · rw [(LocallyConstant.charFn_eq_zero k _ hU).mpr hU', mul_zero, mul_zero]

/-- **The tower identity** `p τ_m = ∑_n P_{nm} τ_n`. -/
theorem mul_towerElem_eq_sum {U : Set X} (hU : IsClopen U) {x₀ : X} (S N : Finset ℤ)
    (f : ℤ → LocallyConstant X k)
    (hconst : ∀ j ∈ S, ∀ n ∈ N, ∀ z ∈ U, f j ((T ^ n) z) = f j ((T ^ n) x₀)) {m : ℤ}
    (hm : ∀ j ∈ S, j + m ∈ N) :
    (∑ j ∈ S, coeff T k (f j) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) *
        towerElem T k hU m =
      ∑ n ∈ N, scal T k (∑ j ∈ S, if j + m = n then f j ((T ^ n) x₀) else 0) *
        towerElem T k hU n := by
  rw [Finset.sum_mul]
  calc ∑ j ∈ S, coeff T k (f j) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        towerElem T k hU m
      = ∑ j ∈ S, scal T k (f j ((T ^ (j + m)) x₀)) * towerElem T k hU (j + m) :=
        Finset.sum_congr rfl fun j hj => coeff_mul_unit_zpow_mul_towerElem T k hU (f j) j m
          (hconst j hj (j + m) (hm j hj))
    _ = ∑ j ∈ S, ∑ n ∈ N,
          if j + m = n then scal T k (f j ((T ^ n) x₀)) * towerElem T k hU n else 0 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.sum_ite_eq, if_pos (hm j hj)]
    _ = ∑ n ∈ N, ∑ j ∈ S,
          if j + m = n then scal T k (f j ((T ^ n) x₀)) * towerElem T k hU n else 0 :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp

/-- `p · ∑_m ρ_m τ_m = ∑_n (∑_m ρ_m P_{nm}) τ_n`. -/
theorem mul_sum_scal_mul_towerElem {U : Set X} (hU : IsClopen U) {x₀ : X} (S F N : Finset ℤ)
    (f : ℤ → LocallyConstant X k)
    (hconst : ∀ j ∈ S, ∀ n ∈ N, ∀ z ∈ U, f j ((T ^ n) z) = f j ((T ^ n) x₀))
    (hbound : ∀ m ∈ F, ∀ j ∈ S, j + m ∈ N) (ρ : F → k) :
    (∑ j ∈ S, coeff T k (f j) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) *
        ∑ m : F, scal T k (ρ m) * towerElem T k hU m =
      ∑ n ∈ N, scal T k (∑ m : F, ρ m *
          ∑ j ∈ S, if j + (m : ℤ) = n then f j ((T ^ n) x₀) else 0) * towerElem T k hU n := by
  have hcent : ∀ (c : k) (x : ClopenCrossedProduct T k), x * scal T k c = scal T k c * x :=
    fun c x => Semigroup.mem_center_iff.mp (SimpleKazhdanSofic.coeff_const_mem_center T k c) x
  rw [Finset.mul_sum]
  calc ∑ m : F, (∑ j ∈ S, coeff T k (f j) *
          ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) *
          (scal T k (ρ m) * towerElem T k hU m)
      = ∑ m : F, ∑ n ∈ N, scal T k (ρ m * ∑ j ∈ S,
          if j + (m : ℤ) = n then f j ((T ^ n) x₀) else 0) * towerElem T k hU n := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← mul_assoc, hcent, mul_assoc, mul_towerElem_eq_sum T k hU S N f hconst (hbound m m.2),
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_mul, mul_assoc]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_sum, Finset.sum_mul]

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ClopenCrossedProduct T k)
    (g : Multiplicative ℤ) :
    SkewMonoidAlgebra.coeff (∑ i ∈ s, x i) g = ∑ i ∈ s, SkewMonoidAlgebra.coeff (x i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply,
      ih]

theorem scal_mul_towerElem {U : Set X} (hU : IsClopen U) (c : k) (m : ℤ) :
    scal T k c * towerElem T k hU m =
      SkewMonoidAlgebra.single (ofAdd m) (ClopenCoeff.of T k (LocallyConstant.const X c *
        LocallyConstant.comap ⟨⇑(T ^ (-m)), (T ^ (-m)).continuous⟩
          (LocallyConstant.charFn k hU))) := by
  rw [scal_apply, towerElem, ← mul_assoc, ← map_mul, SimpleKazhdanSofic.coeff_mul_unit_zpow_eq_single]

/-- The coefficient of `u^{m₀}` in `∑_m ρ_m τ_m`, evaluated at `T^{m₀} x₀`, is `ρ_{m₀}`. -/
theorem coeff_sum_scal_mul_towerElem {U : Set X} (hU : IsClopen U) {x₀ : X} (hx₀ : x₀ ∈ U)
    {F : Finset ℤ} (ρ : F → k) (m₀ : F) :
    (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff
        (∑ m : F, scal T k (ρ m) * towerElem T k hU m) (ofAdd (m₀ : ℤ))) ((T ^ (m₀ : ℤ)) x₀) =
      ρ m₀ := by
  classical
  have hy : (T ^ (-(m₀ : ℤ))) ((T ^ (m₀ : ℤ)) x₀) = x₀ := by
    rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  rw [coeff_finset_sum, Finset.sum_eq_single m₀]
  · rw [scal_mul_towerElem, SkewMonoidAlgebra.coeff_single_apply, if_pos rfl,
      RingEquiv.symm_apply_apply, LocallyConstant.mul_apply, LocallyConstant.coe_comap_apply]
    show LocallyConstant.const X (ρ m₀) ((T ^ (m₀ : ℤ)) x₀) *
      (LocallyConstant.charFn k hU) ((T ^ (-(m₀ : ℤ))) ((T ^ (m₀ : ℤ)) x₀)) = ρ m₀
    rw [hy, (LocallyConstant.charFn_eq_one k x₀ hU).mpr hx₀, mul_one, LocallyConstant.coe_const,
      Function.const_apply]
  · intro m _ hm
    rw [scal_mul_towerElem, SkewMonoidAlgebra.coeff_single_apply,
      if_neg fun h => hm (Subtype.ext (ofAdd.injective h))]
  · intro h
    exact absurd (Finset.mem_univ m₀) h

omit [Field k] in
/-- **One small cylinder**: a clopen set through `x₀` on which finitely many translated
coefficients are constant. -/
theorem exists_clopen_const (x₀ : X) (S N : Finset ℤ) (f : ℤ → LocallyConstant X k) :
    ∃ U : Set X, IsClopen U ∧ x₀ ∈ U ∧
      ∀ j ∈ S, ∀ n ∈ N, ∀ z ∈ U, f j ((T ^ n) z) = f j ((T ^ n) x₀) := by
  refine ⟨⋂ j ∈ S, ⋂ n ∈ N, (T ^ n) ⁻¹' {z | f j z = f j ((T ^ n) x₀)}, ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset fun j _ => isClopen_biInter_finset fun n _ =>
      ((f j).isLocallyConstant.isClopen_fiber _).preimage (T ^ n).continuous
  · exact Set.mem_iInter₂.mpr fun j _ => Set.mem_iInter₂.mpr fun n _ => rfl
  · intro j hj n hn z hz
    exact Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hz j hj) n hn

/-- **The dimension count**: `2|F| > |N|` columns in `k^N` satisfy a nontrivial relation. -/
theorem exists_nontrivial_relation (F N : Finset ℤ) (P Q : ℤ → ℤ → k)
    (hcard : N.card < 2 * F.card) :
    ∃ g : F ⊕ F → k,
      (∀ n ∈ N, ∑ m : F, g (Sum.inl m) * P n m + ∑ m : F, g (Sum.inr m) * Q n m = 0) ∧
        ∃ i, g i ≠ 0 := by
  classical
  have hnli : ¬ LinearIndependent k
      (Sum.elim (fun (m : F) (n : N) => P n m) (fun (m : F) (n : N) => Q n m)) := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_coe,
      Fintype.card_coe] at h
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
  refine ⟨g, fun n hn => ?_, i, hi⟩
  have h := congrFun hg ⟨n, hn⟩
  rw [Fintype.sum_sum_type] at h
  simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Sum.elim_inl, Sum.elim_inr,
    smul_eq_mul, Pi.zero_apply] using h

/-- **Pair dependence**: any two elements `p, q` of `LC(X, k) ⋊_T ℤ` have `(r, s) ≠ 0` with
`pr + qs = 0`, by a dimension count on a tower over one cylinder. -/
theorem exists_pair_dependence [Nonempty X] (p q : ClopenCrossedProduct T k) :
    ∃ r s : ClopenCrossedProduct T k, (r, s) ≠ 0 ∧ p * r + q * s = 0 := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨Sp, fp, hp⟩ := exists_sum_coeff_mul_unit_zpow T k p
  obtain ⟨Sq, fq, hq⟩ := exists_sum_coeff_mul_unit_zpow T k q
  obtain ⟨w, hwp, hwq⟩ : ∃ w : ℕ, (∀ j ∈ Sp, j.natAbs ≤ w) ∧ ∀ j ∈ Sq, j.natAbs ≤ w :=
    ⟨(Sp ∪ Sq).sup Int.natAbs, fun j hj => Finset.le_sup (Finset.mem_union_left Sq hj),
      fun j hj => Finset.le_sup (Finset.mem_union_right Sp hj)⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset ℤ, F = Finset.Icc 0 (2 * (w : ℤ)) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Finset ℤ, N = Finset.Icc (-(w : ℤ)) (3 * (w : ℤ)) := ⟨_, rfl⟩
  have hbound : ∀ S : Finset ℤ, (∀ j ∈ S, j.natAbs ≤ w) → ∀ m ∈ F, ∀ j ∈ S, j + m ∈ N := by
    intro S hS m hm j hj
    have h1 := hS j hj
    rw [hF, Finset.mem_Icc] at hm
    rw [hN, Finset.mem_Icc]
    rcases Int.natAbs_eq j with h | h <;> omega
  have hcard : N.card < 2 * F.card := by
    rw [hF, hN, Int.card_Icc, Int.card_Icc]
    omega
  obtain ⟨Up, hUp, hxp, hcp⟩ := exists_clopen_const T k x₀ Sp N fp
  obtain ⟨Uq, hUq, hxq, hcq⟩ := exists_clopen_const T k x₀ Sq N fq
  obtain ⟨g, hg, i, hi⟩ := exists_nontrivial_relation k F N
    (fun n m => ∑ j ∈ Sp, if j + m = n then fp j ((T ^ n) x₀) else 0)
    (fun n m => ∑ j ∈ Sq, if j + m = n then fq j ((T ^ n) x₀) else 0) hcard
  have hU : IsClopen (Up ∩ Uq) := hUp.inter hUq
  have hx₀ : x₀ ∈ Up ∩ Uq := ⟨hxp, hxq⟩
  refine ⟨∑ m : F, scal T k (g (Sum.inl m)) * towerElem T k hU m,
    ∑ m : F, scal T k (g (Sum.inr m)) * towerElem T k hU m, fun h => ?_, ?_⟩
  · rw [Prod.mk_eq_zero] at h
    rcases i with m₀ | m₀
    · have h1 := coeff_sum_scal_mul_towerElem T k hU hx₀ (fun m => g (Sum.inl m)) m₀
      rw [h.1, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero,
        LocallyConstant.zero_apply] at h1
      exact hi h1.symm
    · have h1 := coeff_sum_scal_mul_towerElem T k hU hx₀ (fun m => g (Sum.inr m)) m₀
      rw [h.2, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero,
        LocallyConstant.zero_apply] at h1
      exact hi h1.symm
  · rw [hp, hq,
      mul_sum_scal_mul_towerElem T k hU Sp F N fp (fun j hj n hn z hz => hcp j hj n hn z hz.1)
        (hbound Sp hwp),
      mul_sum_scal_mul_towerElem T k hU Sq F N fq (fun j hj n hn z hz => hcq j hj n hn z hz.2)
        (hbound Sq hwq), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [← add_mul, ← map_add, hg n hn, map_zero, zero_mul]

/-- **Printed pair dependence**, at the generality of the count: every nonempty space, every
homeomorphism and every field. -/
def PrintedPairDependenceClopenCrossedProduct : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [Nonempty X] (T : X ≃ₜ X) (k : Type) [Field k]
    (p q : ClopenCrossedProduct T k), ∃ r s : ClopenCrossedProduct T k, (r, s) ≠ 0 ∧ p * r + q * s = 0

theorem printedPairDependenceClopenCrossedProduct : PrintedPairDependenceClopenCrossedProduct :=
  fun _ _ _ T k _ p q => exists_pair_dependence T k p q

end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.mul_towerElem_eq_sum
#audit_axioms GroupApproximation.Full.StepanovMatui.exists_nontrivial_relation
#audit_axioms GroupApproximation.Full.StepanovMatui.exists_pair_dependence
#audit_closed_axioms GroupApproximation.Full.StepanovMatui.printedPairDependenceClopenCrossedProduct
