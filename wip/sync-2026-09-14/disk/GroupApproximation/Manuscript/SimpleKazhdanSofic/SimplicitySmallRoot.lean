import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicitySmallSets
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicityCommutationCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Some `e_{ij}(e_V)` with `V` small does not commute with `g`

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, subsection "Simplicity", tex l.197–211, for
`EL_n`, `n ≥ 3` ("for `n ≥ 3` replace `3` by `n` throughout", tex l.97–98):

> Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$. [...] If $g$ commuted with every
> such $h$, then $g_{pi}e_V=0$ for all small $V$ and all $p\ne i$, so $g$ would be diagonal. In
> $g_{ii}e_V=e_Vg_{jj}$ the coefficients at $u^t$ with $t\ne0$ are supported in the disjoint sets
> $T^tV$ and $V$, so they vanish, and as above the coefficients of $g_{ii}$ and $g_{jj}$ at these
> $u^t$ vanish. The constant coefficients agree on every small $V$, hence everywhere, since every
> nonempty clopen set contains a small one. So $g=cI_3$ with $c\in\LC(X,\F_2)$, and comparing
> constant coefficients in $cc^{-1}=1$ gives $c=1$ and $g=1$, a contradiction.

* `smallRoot_eq_zero_of_forall_mul_charFn`, `smallRoot_eq_zero_of_forall_charFn_mul`: `c e_V = 0`
  (resp. `e_V c = 0`) for every small nonempty `V` forces `c = 0` ("as above");
* `smallRoot_offDiag_eq_zero`: `g` is diagonal;
* `smallRoot_coeff_diag_eq_zero`: the coefficients of the diagonal entries at `u^t`, `t ≠ 0`, vanish;
* `smallRoot_coeff_one_diag_eq`: the constant coefficients agree;
* `eq_one_of_commute_elGen_small`: `g = 1`;
* `exists_isSmallSet_not_commute_elGen`: the printed sentence l.197.
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic

open GroupApproximation.Pestov91 GroupApproximation.ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X}

theorem smallRoot_toAdd_ne_zero {t : Multiplicative ℤ} (ht : t ≠ 1) : toAdd t ≠ 0 :=
  fun h => ht (by rw [← ofAdd_toAdd t, h, ofAdd_zero])

theorem smallRoot_zpow_apply_zpow_neg (T : X ≃ₜ X) (s : ℤ) (y : X) : (T ^ s) ((T ^ (-s)) y) = y := by
  rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]

/-- In a small set, `T^{-s}y ∈ V` and `y ∈ V` are incompatible for `0 < |s| ≤ w`. -/
theorem smallRoot_notMem_of_zpow_neg_mem {w : ℕ} {F : Finset (LocallyConstant X (ZMod 2))}
    {V : Set X} (hs : IsSmallSet T w F V) {s : ℤ} (hs0 : s ≠ 0) (hsw : |s| ≤ (w : ℤ)) {y : X}
    (hy : (T ^ (-s)) y ∈ V) : y ∉ V := fun hyV =>
  Set.disjoint_left.mp (hs.1 s hs0 (le_trans hsw (by push_cast; omega))) hyV
    ⟨(T ^ (-s)) y, hy, smallRoot_zpow_apply_zpow_neg T s y⟩

section Coefficients

variable [TotallySeparatedSpace X] (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y) (w : ℕ)
  (F : Finset (LocallyConstant X (ZMod 2)))

include hfree

/-- **"As above"**: `c e_V = 0` for every small nonempty clopen `V` forces `c = 0`. -/
theorem smallRoot_eq_zero_of_forall_mul_charFn {c : ClopenCrossedProduct T (ZMod 2)}
    (hc : ∀ (V : Set X) (hV : IsClopen V), V.Nonempty → IsSmallSet T w F V →
      c * coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) = 0) : c = 0 := by
  refine SkewMonoidAlgebra.ext fun t => ?_
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra ht
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_mul_charFn_ne_zero T ht
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmallSet_subset T hfree w F hWc hWne
  exact hW V hVc hVne hVW (by rw [hc V hVc hVne hVs, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply])

/-- **"As above"**: `e_V c = 0` for every small nonempty clopen `V` forces `c = 0`. -/
theorem smallRoot_eq_zero_of_forall_charFn_mul {c : ClopenCrossedProduct T (ZMod 2)}
    (hc : ∀ (V : Set X) (hV : IsClopen V), V.Nonempty → IsSmallSet T w F V →
      coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) * c = 0) : c = 0 := by
  refine SkewMonoidAlgebra.ext fun t => ?_
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra ht
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_charFn_mul_ne_zero T ht
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmallSet_subset T hfree w F hWc hWne
  exact hW V hVc hVne hVW (by rw [hc V hVc hVne hVs, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply])

variable {n : ℕ} (hn : 2 ≤ n) {g : elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))}
  (hg : ∀ (V : Set X) (hV : IsClopen V), V.Nonempty → IsSmallSet T w F V →
    ∀ (i j : Fin n) (hij : i ≠ j),
      Commute g (elGen i j hij (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))))

include hn hg

/-- **tex l.203–205**: `g_{pi} e_V = 0` for all small `V` and `p ≠ i`, so `g` is diagonal. -/
theorem smallRoot_offDiag_eq_zero {p i : Fin n} (hpi : p ≠ i) :
    ((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
      Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p i = 0 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  exact smallRoot_eq_zero_of_forall_mul_charFn hfree w F fun V hV hne hs =>
    ((commute_elGen_iff g (Ne.symm hji) _).mp (hg V hV hne hs i j (Ne.symm hji))).1 p hpi

omit hn in
/-- **tex l.205–208**: in `g_{ii} e_V = e_V g_{jj}` the coefficients at `u^t`, `t ≠ 0`, are
supported in the disjoint sets `T^tV` and `V`, so the coefficients of `g_{ii}` at these `u^t`
vanish. -/
theorem smallRoot_coeff_diag_eq_zero
    (hw : ∀ (p q : Fin n) (t : Multiplicative ℤ),
      t ∈ SkewMonoidAlgebra.support (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p q) → |toAdd t| ≤ (w : ℤ))
    {i j : Fin n} (hij : i ≠ j) {t : Multiplicative ℤ} (ht : t ≠ 1) :
    SkewMonoidAlgebra.coeff (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
      Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) t = 0 := by
  by_contra hc
  have htw : |toAdd t| ≤ (w : ℤ) := hw i i t (SkewMonoidAlgebra.mem_support_iff.mpr hc)
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_mul_charFn_ne_zero T hc
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmallSet_subset T hfree w F hWc hWne
  refine hW V hVc hVne hVW ?_
  have hcomm := ((commute_elGen_iff g hij _).mp (hg V hVc hVne hVs i j hij)).2.2
  refine (ClopenCoeff.of T (ZMod 2)).symm.injective (LocallyConstant.ext fun y => ?_)
  rw [map_zero, LocallyConstant.zero_apply]
  by_cases hy : (T ^ (-toAdd t)) y ∈ V
  · rw [hcomm, coeff_charFn_mul_apply, LocallyConstant.coe_charFn,
      Set.indicator_of_notMem (smallRoot_notMem_of_zpow_neg_mem hVs (smallRoot_toAdd_ne_zero ht) htw hy),
      zero_mul]
  · rw [coeff_mul_charFn_apply, LocallyConstant.coe_charFn, Set.indicator_of_notMem hy, mul_zero]

omit hn in
/-- **tex l.208–209**: the constant coefficients of `g_{ii}` and `g_{jj}` agree on every small
`V`, hence everywhere, since every nonempty clopen set contains a small one. -/
theorem smallRoot_coeff_one_diag_eq {i j : Fin n} (hij : i ≠ j) :
    (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) 1) =
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) j j) 1) := by
  by_contra hne
  have hA : IsClopen {y : X | ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) 1) -
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) j j) 1)) y ≠ 0} := by
    simpa only [Set.compl_setOf, ne_eq] using
      (LocallyConstant.isLocallyConstant _).isClopen_fiber (0 : ZMod 2) |>.compl
  have hAne : {y : X | ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) 1) -
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) j j) 1)) y ≠ 0}.Nonempty := by
    by_contra h0
    apply hne
    ext y
    have hy : ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) 1) -
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) j j) 1)) y = 0 := by
      by_contra h1
      exact h0 ⟨y, h1⟩
    rwa [LocallyConstant.sub_apply, sub_eq_zero] at hy
  obtain ⟨V, hVc, ⟨y, hy⟩, hVA, hVs⟩ := exists_isSmallSet_subset T hfree w F hA hAne
  have hcomm := ((commute_elGen_iff g hij _).mp (hg V hVc ⟨y, hy⟩ hVs i j hij)).2.2
  have h1 : (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        ((((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i i) *
          coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hVc)) 1) y =
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hVc) *
          (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
            Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) j j)) 1) y := by
    rw [hcomm]
  rw [coeff_mul_charFn_apply, coeff_charFn_mul_apply, toAdd_one, neg_zero, zpow_zero,
    Homeomorph.one_apply, LocallyConstant.coe_charFn, Set.indicator_of_mem hy, Pi.one_apply,
    mul_one, one_mul] at h1
  exact hVA hy (by rw [LocallyConstant.sub_apply, h1, sub_self])

/-- **tex l.197–211**: if `g ∈ EL_n(R)` commutes with `e_{ij}(e_V)` for every small nonempty clopen
`V` and all `i ≠ j`, and `w` bounds the exponents of the entries of `g`, then `g = 1`. -/
theorem eq_one_of_commute_elGen_small
    (hw : ∀ (p q : Fin n) (t : Multiplicative ℤ),
      t ∈ SkewMonoidAlgebra.support (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p q) → |toAdd t| ≤ (w : ℤ)) :
    g = 1 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hzero : ∀ (p : Fin n) {t : Multiplicative ℤ}, t ≠ 1 →
      SkewMonoidAlgebra.coeff (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p p) t = 0 := by
    intro p t ht
    obtain ⟨j, hjp⟩ := exists_ne p
    exact smallRoot_coeff_diag_eq_zero hfree w F hg hw (Ne.symm hjp) ht
  -- every diagonal entry equals `g_{i₀ i₀}`
  have hdiag : ∀ p : Fin n,
      (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p p) =
      (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) := by
    intro p
    refine SkewMonoidAlgebra.ext fun t => ?_
    by_cases ht : t = 1
    · subst ht
      by_cases hp : p = i₀
      · rw [hp]
      · exact (ClopenCoeff.of T (ZMod 2)).symm.injective
          (smallRoot_coeff_one_diag_eq hfree w F hg hp)
    · rw [hzero p ht, hzero i₀ ht]
  -- `g = c I_n`
  have hscalar : ((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) =
      Matrix.scalar (Fin n) (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) := by
    ext p q
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · rw [if_pos hpq, hpq, hdiag q]
    · rw [if_neg hpq, smallRoot_offDiag_eq_zero hfree w F hn hg hpq]
  -- `c ∈ LC(X, F₂)`
  have hc0 : (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) =
      coeff T (ZMod 2) ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) 1)) :=
    eq_coeff_of_coeff_eq_zero T (ZMod 2) fun t ht => hzero i₀ ht
  -- `c c⁻¹ = 1`
  have hinv : (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) *
      ((((g⁻¹ : elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) :
        (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) = 1 := by
    have h1 : ((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) *
        (((g⁻¹ : elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) :
          (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) = 1 := by
      rw [Subgroup.coe_inv, Units.mul_inv]
    rw [hscalar] at h1
    simpa [Matrix.scalar_apply] using congrFun (congrFun h1 i₀) i₀
  -- comparing constant coefficients gives `c = 1`
  have hf1 : (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) 1) = 1 := by
    have h2 : (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
          ((((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
            Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) *
          ((((g⁻¹ : elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) :
            (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
              Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀)) 1) =
        (ClopenCoeff.of T (ZMod 2)).symm
          (SkewMonoidAlgebra.coeff (1 : ClopenCrossedProduct T (ZMod 2)) 1) := by
      rw [hinv]
    rw [hc0, coeff_apply, Pestov91.CrossedProduct.C_apply, SkewMonoidAlgebra.coeff_single_one_mul,
      map_mul, RingEquiv.symm_apply_apply, SkewMonoidAlgebra.coeff_one_one, map_one] at h2
    ext y
    have hy := LocallyConstant.congr_fun h2 y
    rw [LocallyConstant.mul_apply, LocallyConstant.one_apply] at hy
    rw [LocallyConstant.one_apply]
    have hvals : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide
    exact hvals _ _ hy
  have hc1 : (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
      Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i₀ i₀) = 1 := by
    rw [hc0, hf1, map_one]
  apply Subtype.ext
  apply Units.ext
  rw [hscalar, hc1]
  simp

omit hg in
/-- **tex l.197, as printed**: for `1 ≠ g ∈ EL_n(R)` with exponent bound `w`, some `h = e_{ij}(e_V)`
with `V` small and nonempty does not commute with `g`. -/
theorem exists_isSmallSet_not_commute_elGen
    (hw : ∀ (p q : Fin n) (t : Multiplicative ℤ),
      t ∈ SkewMonoidAlgebra.support (((g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) p q) → |toAdd t| ≤ (w : ℤ))
    (hg1 : g ≠ 1) :
    ∃ (V : Set X) (hV : IsClopen V), V.Nonempty ∧ IsSmallSet T w F V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        ¬ Commute g (elGen i j hij (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))) := by
  by_contra hne
  refine hg1 (eq_one_of_commute_elGen_small hfree w F hn (fun V hV hVne hs i j hij => ?_) hw)
  by_contra hc
  exact hne ⟨V, hV, hVne, hs, i, j, hij, hc⟩

end Coefficients

end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.smallRoot_eq_zero_of_forall_mul_charFn
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.smallRoot_offDiag_eq_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.smallRoot_coeff_diag_eq_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.smallRoot_coeff_one_diag_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.eq_one_of_commute_elGen_small
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_isSmallSet_not_commute_elGen
