import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingPartitions
import GroupApproximation.Dynamics.ClopenSwapInvolution
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower matrix units `E_ab(W)` (simple_kazhdan_sofic_group.tex, tex 154–161)

`simple_kazhdan_sofic_group.tex` at bf961c128, "A finite tower detects every normal subgroup", tex
155–161:

> Suppose the levels $T^aU$ are disjoint for all indices needed below. For $|a|,|b|\le m$ and clopen
> $W\subseteq U$, put $E_{ab}(W)=e_{T^aW}u^{a-b}$. These satisfy
> $E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$.

The levels needed are `T^aU`, `|a| ≤ m`, together with the translates `T^{a-b+c}U` met in a product.
So the hypothesis is `U ∩ T^jU = ∅` for `0 < |j| ≤ 2m`, the one used in `towerE_mul_towerE`.

* `towerE T k hW a b = e_{T^aW} u^{a-b}`;
* `eU_mul_eU`, `eU_mul_eU_of_disjoint`, `unit_zpow_mul_eU`: `e_V e_{V'} = e_{V ∩ V'}`, `0` for
  disjoint sets, and `u^j e_V = e_{T^jV} u^j`;
* `towerE_mul_towerE`: the matrix unit relations.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open ClopenCrossedProduct

variable {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y) (k : Type*) [Ring k]

theorem charFn_mul_charFn_inter {U V : Set Y} (hU : IsClopen U) (hV : IsClopen V) :
    LocallyConstant.charFn k hU * LocallyConstant.charFn k hV =
      LocallyConstant.charFn k (hU.inter hV) := by
  ext y
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn]
  by_cases hyU : y ∈ U
  · by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyV,
        Set.indicator_of_mem (show y ∈ U ∩ V from ⟨hyU, hyV⟩), Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hyV,
        Set.indicator_of_notMem (show y ∉ U ∩ V from fun h => hyV h.2), mul_zero]
  · rw [Set.indicator_of_notMem hyU,
      Set.indicator_of_notMem (show y ∉ U ∩ V from fun h => hyU h.1), zero_mul]

theorem eU_congr {V V' : Set Y} (hV : IsClopen V) (hV' : IsClopen V') (h : V = V') :
    eU T k hV = eU T k hV' := by
  subst h
  rfl

theorem eU_mul_eU {V V' : Set Y} (hV : IsClopen V) (hV' : IsClopen V') :
    eU T k hV * eU T k hV' = eU T k (hV.inter hV') := by
  rw [eU, eU, ← map_mul, charFn_mul_charFn_inter]
  rfl

theorem eU_mul_eU_of_disjoint {V V' : Set Y} (hV : IsClopen V) (hV' : IsClopen V')
    (h : Disjoint V V') : eU T k hV * eU T k hV' = 0 := by
  rw [eU, eU, ← map_mul, charFn_mul_charFn_of_disjoint k hV hV' h, map_zero]

/-- `u^j e_V = e_{T^jV} u^j`. -/
theorem unit_zpow_mul_eU (j : ℤ) {V : Set Y} (hV : IsClopen V) :
    ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) * eU T k hV =
      eU T k (isClopen_image (T ^ j) hV) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) :=
  unit_zpow_mul_charFn T k j hV

theorem image_zpow_image (i j : ℤ) (V : Set Y) :
    ⇑(T ^ i) '' (⇑(T ^ j) '' V) = ⇑(T ^ (i + j)) '' V := by
  rw [Set.image_image]
  exact Set.image_congr fun y _ => Dynamics.zpow_apply_zpow_apply T i j y

/-- `E_ab(W) = e_{T^aW} u^{a-b}` (tex 156–159). -/
noncomputable def towerE {W : Set Y} (hW : IsClopen W) (a b : ℤ) : ClopenCrossedProduct T k :=
  eU T k (isClopen_image (T ^ a) hW) *
    ((unit T k ^ (a - b) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

/-- The product of two tower units in normal form. -/
theorem towerE_mul_towerE_eq {W W' : Set Y} (hW : IsClopen W) (hW' : IsClopen W') (a b c d : ℤ) :
    towerE T k hW a b * towerE T k hW' c d =
      eU T k (isClopen_image (T ^ a) hW) *
          eU T k (isClopen_image (T ^ (a - b)) (isClopen_image (T ^ c) hW')) *
        ((unit T k ^ (a - b + (c - d)) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  calc towerE T k hW a b * towerE T k hW' c d
      = eU T k (isClopen_image (T ^ a) hW) *
          (((unit T k ^ (a - b) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
            eU T k (isClopen_image (T ^ c) hW')) *
          ((unit T k ^ (c - d) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
        simp only [towerE, mul_assoc]
    _ = eU T k (isClopen_image (T ^ a) hW) *
          (eU T k (isClopen_image (T ^ (a - b)) (isClopen_image (T ^ c) hW')) *
            ((unit T k ^ (a - b) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) *
          ((unit T k ^ (c - d) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
        rw [unit_zpow_mul_eU]
    _ = eU T k (isClopen_image (T ^ a) hW) *
          eU T k (isClopen_image (T ^ (a - b)) (isClopen_image (T ^ c) hW')) *
          (((unit T k ^ (a - b) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
            ((unit T k ^ (c - d) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) := by
        simp only [mul_assoc]
    _ = _ := by rw [← Units.val_mul, ← zpow_add]

/-- **The matrix unit relations** (tex 160–161): `E_ab(W) E_cd(W') = δ_bc E_ad(W ∩ W')`, when
`U ∩ T^jU = ∅` for `0 < |j| ≤ 2m`, `W, W' ⊆ U` and `|b|, |c| ≤ m`. -/
theorem towerE_mul_towerE {U W W' : Set Y} (hW : IsClopen W) (hW' : IsClopen W') (hWU : W ⊆ U)
    (hW'U : W' ⊆ U) {m : ℕ}
    (hdisj : ∀ j : ℤ, j ≠ 0 → |j| ≤ 2 * (m : ℤ) → Disjoint U (⇑(T ^ j) '' U))
    {a b c d : ℤ} (hb : |b| ≤ m) (hc : |c| ≤ m) :
    towerE T k hW a b * towerE T k hW' c d =
      if b = c then towerE T k (hW.inter hW') a d else 0 := by
  rw [towerE_mul_towerE_eq]
  split_ifs with hbc
  · subst hbc
    have hset : ⇑(T ^ a) '' W ∩ ⇑(T ^ (a - b)) '' (⇑(T ^ b) '' W') = ⇑(T ^ a) '' (W ∩ W') := by
      rw [image_zpow_image, sub_add_cancel, Set.image_inter (T ^ a).injective]
    rw [eU_mul_eU, eU_congr T k _ (isClopen_image (T ^ a) (hW.inter hW')) hset,
      sub_add_sub_cancel]
    rfl
  · have hj : c - b ≠ 0 := sub_ne_zero.2 (Ne.symm hbc)
    have hjb : |c - b| ≤ 2 * (m : ℤ) := by
      obtain ⟨hb1, hb2⟩ := abs_le.1 hb
      obtain ⟨hc1, hc2⟩ := abs_le.1 hc
      exact abs_le.2 ⟨by omega, by omega⟩
    have hdis : Disjoint (⇑(T ^ a) '' W) (⇑(T ^ (a - b)) '' (⇑(T ^ c) '' W')) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ hz
      rw [image_zpow_image] at hz
      obtain ⟨w', hw', hww'⟩ := hz
      have hback : (T ^ (a - b + c - a)) w' = w := Dynamics.zpow_sub_apply_of_eq T hww'.symm
      rw [show a - b + c - a = c - b by ring] at hback
      exact Set.disjoint_left.1 (hdisj (c - b) hj hjb) (hWU hw) ⟨w', hW'U hw', hback⟩
    rw [eU_mul_eU_of_disjoint T k _ _ hdis, zero_mul]

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.eU_mul_eU
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerE_mul_towerE
