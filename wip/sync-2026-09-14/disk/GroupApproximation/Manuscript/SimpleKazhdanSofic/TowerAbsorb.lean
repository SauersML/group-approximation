import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerUnits
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.ZMod.Basic

/-!
# Absorption into a larger tower (simple_kazhdan_sofic_group.tex, tex 162–173)

`simple_kazhdan_sofic_group.tex` at bf961c128, tex 162–173:

> Their span is a subring $B_m(U)\cong M_{2m+1}(\LC(U,\F_2))$, with unit
> $e_{\bigcup_{|a|\le m}T^aU}$. If $r,r'$ involve only powers $u^j$ with $|j|\le w$, then
> \begin{equation}\label{eq:absorb} rB_m(U)r'\subseteq B_{m+w}(U), \end{equation}
> provided the larger tower is disjoint. To see this, multiplying $E_{ab}(W)$ on the left by $fu^i$
> and on the right by $f'u^j$ changes its indices to $(a+i,b-j)$ and restricts its clopen
> coefficient.

* `towerSpan T U m`: the `F₂`-span `B_m(U)` of the `E_ab(W)`, with `W ⊆ U` clopen and `|a|, |b| ≤ m`.
  Over `F₂` the span is the additive subgroup they generate;
* `InvolvesPowersAtMost T w r`: every Laurent exponent of `r` has absolute value at most `w`;
* `coeff_mul_unit_mul_towerE_mul_coeff_mul_unit`: `f u^i E_ab(W) f' u^j = E_{a+i,b-j}(W₁)` with the
  restricted clopen coefficient `W₁ ⊆ W` (tex 171–173);
* `mul_mem_towerSpan_mul`: **eq:absorb** (tex 166–170).

The span membership needs no disjointness. Disjointness of the larger tower is what makes
`B_{m+w}(U)` a ring with the matrix unit relations (`towerE_mul_towerE`); the printed proviso is used
there.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

variable {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y)

/-- `B_m(U)`, the `F₂`-span of the tower units over `U` (tex 162). -/
def towerSpan (U : Set Y) (m : ℕ) : AddSubgroup (ClopenCrossedProduct T (ZMod 2)) :=
  AddSubgroup.closure {x | ∃ (W : Set Y) (hW : IsClopen W), W ⊆ U ∧
    ∃ a b : ℤ, |a| ≤ m ∧ |b| ≤ m ∧ x = towerE T (ZMod 2) hW a b}

/-- `r` involves only powers `u^j` with `|j| ≤ w` (tex 166–167). -/
def InvolvesPowersAtMost {k : Type*} [Ring k] (w : ℕ) (r : ClopenCrossedProduct T k) : Prop :=
  ∀ g ∈ SkewMonoidAlgebra.support r, |toAdd g| ≤ w

theorem single_eq_coeff_mul_unit_zpow {k : Type*} [Ring k] (g : Multiplicative ℤ)
    (c : ClopenCoeff T k) :
    (SkewMonoidAlgebra.single g c : ClopenCrossedProduct T k) =
      coeff T k ((ClopenCoeff.of T k).symm c) *
        ((unit T k ^ toAdd g : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, ofAdd_toAdd, coeff_apply, RingEquiv.apply_symm_apply,
    Pestov91.CrossedProduct.C_mul_single, mul_one]

/-- The restricted clopen coefficient `W₁ = {y ∈ W : g(T^n y) = 1}`. -/
theorem isClopen_restrictCoeff {W : Set Y} (hW : IsClopen W) (n : ℤ)
    (g : LocallyConstant Y (ZMod 2)) : IsClopen (W ∩ ⇑(T ^ n) ⁻¹' {z | g z = 1}) :=
  hW.inter ((g.isLocallyConstant.isClopen_fiber 1).preimage (T ^ n).continuous)

/-- Over `F₂`, `g e_{T^nW} = e_{T^nW₁}`: multiplying by a coefficient restricts the clopen set. -/
theorem coeff_mul_eU_eq_eU_restrict {W : Set Y} (hW : IsClopen W) (n : ℤ)
    (g : LocallyConstant Y (ZMod 2)) :
    coeff T (ZMod 2) g * eU T (ZMod 2) (isClopen_image (T ^ n) hW) =
      eU T (ZMod 2) (isClopen_image (T ^ n) (isClopen_restrictCoeff T hW n g)) := by
  rw [eU, eU, ← map_mul]
  congr 1
  ext z
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn]
  by_cases hz : z ∈ ⇑(T ^ n) '' W
  · obtain ⟨y, hy, rfl⟩ := hz
    rw [Set.indicator_of_mem ⟨y, hy, rfl⟩, Pi.one_apply, mul_one]
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 (g ((T ^ n) y)) with h0 | h1
    · rw [h0, Set.indicator_of_notMem]
      rintro ⟨y', ⟨_, hy'⟩, hyy'⟩
      have hyy : y' = y := (T ^ n).injective hyy'
      rw [hyy] at hy'
      exact zero_ne_one (h0.symm.trans hy')
    · rw [h1, Set.indicator_of_mem ⟨y, ⟨hy, h1⟩, rfl⟩, Pi.one_apply]
  · rw [Set.indicator_of_notMem hz, mul_zero, Set.indicator_of_notMem]
    rintro ⟨y, ⟨hy, _⟩, rfl⟩
    exact hz ⟨y, hy, rfl⟩

/-- **The absorption step** (tex 171–173): `f u^i E_ab(W) f' u^j = E_{a+i,b-j}(W₁)` over `F₂`, with
the restricted clopen coefficient `W₁ ⊆ W`. -/
theorem coeff_mul_unit_mul_towerE_mul_coeff_mul_unit {W : Set Y} (hW : IsClopen W)
    (f f' : LocallyConstant Y (ZMod 2)) (i a b j : ℤ) :
    ∃ (W₁ : Set Y) (hW₁ : IsClopen W₁), W₁ ⊆ W ∧
      coeff T (ZMod 2) f *
          ((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
            ClopenCrossedProduct T (ZMod 2)) *
          towerE T (ZMod 2) hW a b *
          (coeff T (ZMod 2) f' *
            ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2))) =
        towerE T (ZMod 2) hW₁ (a + i) (b - j) := by
  obtain ⟨σf', hσdef⟩ : ∃ σf' : LocallyConstant Y (ZMod 2),
      σf' = (ClopenCoeff.of T (ZMod 2)).symm (ofAdd (i + a - b) • ClopenCoeff.of T (ZMod 2) f') :=
    ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : LocallyConstant Y (ZMod 2), g = f * σf' := ⟨_, rfl⟩
  refine ⟨W ∩ ⇑(T ^ (i + a)) ⁻¹' {z | g z = 1}, isClopen_restrictCoeff T hW (i + a) g,
    Set.inter_subset_left, ?_⟩
  have hu1 : ((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
        ClopenCrossedProduct T (ZMod 2)) * eU T (ZMod 2) (isClopen_image (T ^ a) hW) =
      eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
        ((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
          ClopenCrossedProduct T (ZMod 2)) := by
    rw [unit_zpow_mul_eU, eU_congr T (ZMod 2) _ (isClopen_image (T ^ (i + a)) hW)
      (image_zpow_image T i a W)]
  have hu2 : ((unit T (ZMod 2) ^ (i + a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
        ClopenCrossedProduct T (ZMod 2)) * coeff T (ZMod 2) f' =
      coeff T (ZMod 2) σf' *
        ((unit T (ZMod 2) ^ (i + a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
          ClopenCrossedProduct T (ZMod 2)) := by
    rw [coeff_apply, coeff_apply, hσdef, RingEquiv.apply_symm_apply]
    exact Pestov91.CrossedProduct.unit_zpow_mul_C (i + a - b) (ClopenCoeff.of T (ZMod 2) f')
  have hcomm : eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) * coeff T (ZMod 2) σf' =
      coeff T (ZMod 2) σf' * eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) := by
    rw [eU, ← map_mul, ← map_mul, mul_comm]
  have key : coeff T (ZMod 2) f *
        ((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
          ClopenCrossedProduct T (ZMod 2)) *
        towerE T (ZMod 2) hW a b *
        (coeff T (ZMod 2) f' *
          ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
            ClopenCrossedProduct T (ZMod 2))) =
      coeff T (ZMod 2) g * eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
        ((unit T (ZMod 2) ^ (a + i - (b - j)) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
          ClopenCrossedProduct T (ZMod 2)) := by
    calc coeff T (ZMod 2) f *
          ((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
            ClopenCrossedProduct T (ZMod 2)) *
          towerE T (ZMod 2) hW a b *
          (coeff T (ZMod 2) f' *
            ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)))
        = coeff T (ZMod 2) f *
            (((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) * eU T (ZMod 2) (isClopen_image (T ^ a) hW)) *
            ((unit T (ZMod 2) ^ (a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) * coeff T (ZMod 2) f' *
            ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) := by
          simp only [towerE, mul_assoc]
      _ = coeff T (ZMod 2) f * eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
            (((unit T (ZMod 2) ^ i : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) *
              ((unit T (ZMod 2) ^ (a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
                ClopenCrossedProduct T (ZMod 2))) * coeff T (ZMod 2) f' *
            ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) := by
          rw [hu1]
          simp only [mul_assoc]
      _ = coeff T (ZMod 2) f * eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
            (((unit T (ZMod 2) ^ (i + a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) * coeff T (ZMod 2) f') *
            ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) := by
          rw [← Units.val_mul, ← zpow_add, add_sub_assoc]
          simp only [mul_assoc]
      _ = coeff T (ZMod 2) f * (eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
            coeff T (ZMod 2) σf') *
            (((unit T (ZMod 2) ^ (i + a - b) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) *
              ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
                ClopenCrossedProduct T (ZMod 2))) := by
          rw [hu2]
          simp only [mul_assoc]
      _ = coeff T (ZMod 2) g * eU T (ZMod 2) (isClopen_image (T ^ (i + a)) hW) *
            ((unit T (ZMod 2) ^ (a + i - (b - j)) : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) := by
          rw [hcomm, ← Units.val_mul, ← zpow_add, show i + a - b + j = a + i - (b - j) by ring,
            ← mul_assoc, ← map_mul, ← hgdef]
  rw [key, coeff_mul_eU_eq_eU_restrict, towerE,
    eU_congr T (ZMod 2) _ (isClopen_image (T ^ (a + i)) (isClopen_restrictCoeff T hW (i + a) g))
      (by rw [add_comm])]

/-- **eq:absorb** (tex 166–170): if `r, r'` involve only powers `u^j` with `|j| ≤ w`, then
`r B_m(U) r' ⊆ B_{m+w}(U)`. -/
theorem mul_mem_towerSpan_mul {U : Set Y} {m w : ℕ} {r r' x : ClopenCrossedProduct T (ZMod 2)}
    (hr : InvolvesPowersAtMost T w r) (hr' : InvolvesPowersAtMost T w r')
    (hx : x ∈ towerSpan T U m) : r * x * r' ∈ towerSpan T U (m + w) := by
  classical
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨W, hW, hWU, a, b, ha, hb, rfl⟩ := hx
    rw [← SkewMonoidAlgebra.sum_single r, ← SkewMonoidAlgebra.sum_single r',
      SkewMonoidAlgebra.sum_def', SkewMonoidAlgebra.sum_def', Finset.sum_mul, Finset.sum_mul_sum]
    refine AddSubgroup.sum_mem _ fun g hg => AddSubgroup.sum_mem _ fun g' hg' => ?_
    rw [single_eq_coeff_mul_unit_zpow T g, single_eq_coeff_mul_unit_zpow T g']
    obtain ⟨W₁, hW₁, hW₁W, heq⟩ := coeff_mul_unit_mul_towerE_mul_coeff_mul_unit T hW
      ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff r g))
      ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff r' g')) (toAdd g) a b (toAdd g')
    rw [heq]
    obtain ⟨ha1, ha2⟩ := abs_le.1 ha
    obtain ⟨hb1, hb2⟩ := abs_le.1 hb
    obtain ⟨hi1, hi2⟩ := abs_le.1 (hr g hg)
    obtain ⟨hj1, hj2⟩ := abs_le.1 (hr' g' hg')
    exact AddSubgroup.subset_closure ⟨W₁, hW₁, hW₁W.trans hWU, a + toAdd g, b - toAdd g',
      abs_le.2 ⟨by push_cast; omega, by push_cast; omega⟩,
      abs_le.2 ⟨by push_cast; omega, by push_cast; omega⟩, rfl⟩
  | zero =>
    rw [mul_zero, zero_mul]
    exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul]
    exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx =>
    rw [mul_neg, neg_mul]
    exact AddSubgroup.neg_mem _ hx

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.coeff_mul_eU_eq_eU_restrict
#audit_axioms GroupApproximation.SimpleKazhdanSofic.coeff_mul_unit_mul_towerE_mul_coeff_mul_unit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.mul_mem_towerSpan_mul
