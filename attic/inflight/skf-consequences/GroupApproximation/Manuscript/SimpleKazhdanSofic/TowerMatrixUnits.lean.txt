import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerStatement
import GroupApproximation.Dynamics.ClopenSwapInvolution

/-!
# Matrix units of a finite clopen tower

`simple_kazhdan_sofic_group.tex` at bf961c128, tex 157–166:

> For $|a|,|b|\le m$ and clopen $W\subseteq U$, put $E_{ab}(W)=e_{T^aW}u^{a-b}$.  These satisfy
> $E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$.

For a clopen `U` whose levels `T^a U`, `|a| ≤ m`, are pairwise disjoint and clopen `W, W' ⊆ U`:

* `towerE_mul_towerE`: the printed product rule;
* `towerE_ne_zero`: `E_{ab}(W) ≠ 0` for nonempty `W`;
* `levelSum W = ∑_a E_{aa}(W)`, the unit of the tower over `W`, commutes with `B_m(U)`
  (`levelSum_mul_eq_mul_levelSum`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ClopenCrossedProduct

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {k : Type*} [Ring k]

/-- `T^i(T^j A) = T^{i+j} A`. -/
theorem image_zpow_image_zpow (T : X ≃ₜ X) (i j : ℤ) (A : Set X) :
    ⇑(T ^ i) '' (⇑(T ^ j) '' A) = ⇑(T ^ (i + j)) '' A := by
  rw [Set.image_image]
  refine congrArg (fun f : X → X => f '' A) (funext fun x => ?_)
  rw [← Homeomorph.mul_apply, ← zpow_add]

theorem charFn_congr {U V : Set X} (hU : IsClopen U) (hV : IsClopen V) (h : U = V) :
    LocallyConstant.charFn k hU = LocallyConstant.charFn k hV := by
  subst h
  rfl

theorem charFn_mul_charFn_inter {U V : Set X} (hU : IsClopen U) (hV : IsClopen V) :
    LocallyConstant.charFn k hU * LocallyConstant.charFn k hV =
      LocallyConstant.charFn k (hU.inter hV) := by
  ext x
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn]
  by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;> simp [hxU, hxV]

variable (T k)

/-- `coeff f * u^i * (coeff g * u^j) = coeff (f * (g ∘ T^{-i})) * u^{i+j}` for indicators. -/
theorem coeff_charFn_mul_unit_mul {V V' : Set X} (hV : IsClopen V) (hV' : IsClopen V') (i j : ℤ) :
    coeff T k (LocallyConstant.charFn k hV) *
          ((unit T k ^ i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        (coeff T k (LocallyConstant.charFn k hV') *
          ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) =
      coeff T k (LocallyConstant.charFn k hV *
          LocallyConstant.charFn k (isClopen_image (T ^ i) hV')) *
        ((unit T k ^ (i + j) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  have key := unit_zpow_mul_charFn T k i hV'
  calc coeff T k (LocallyConstant.charFn k hV) *
          ((unit T k ^ i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
        (coeff T k (LocallyConstant.charFn k hV') *
          ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k))
      = coeff T k (LocallyConstant.charFn k hV) *
          (((unit T k ^ i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
            coeff T k (LocallyConstant.charFn k hV')) *
          ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
        simp only [mul_assoc]
    _ = coeff T k (LocallyConstant.charFn k hV) *
          (coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ i) hV')) *
            ((unit T k ^ i : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) *
          ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
        rw [key]
    _ = coeff T k (LocallyConstant.charFn k hV *
          LocallyConstant.charFn k (isClopen_image (T ^ i) hV')) *
        ((unit T k ^ (i + j) : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
        rw [map_mul, zpow_add, Units.val_mul]
        simp only [mul_assoc]

variable {T k}

/-- **The printed product rule** (tex 161–162): `E_{ab}(W) E_{cd}(W') = δ_{bc} E_{ad}(W ∩ W')`. -/
theorem towerE_mul_towerE {m : ℕ} {U W W' : Set X} (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U)
    (hW'U : W' ⊆ U) (hW : IsClopen W) (hW' : IsClopen W') (a b c d : Fin (2 * m + 1)) :
    towerE T k m hW a b * towerE T k m hW' c d =
      if b = c then towerE T k m (hW.inter hW') a d else 0 := by
  unfold towerE
  rw [coeff_charFn_mul_unit_mul]
  split_ifs with hbc
  · subst hbc
    have hset : ⇑(T ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) '' (⇑(T ^ (((b : ℕ) : ℤ) - m)) '' W') =
        ⇑(T ^ (((a : ℕ) : ℤ) - m)) '' W' := by
      rw [image_zpow_image_zpow]
      congr 2
      ring
    have hexp : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) + (((b : ℕ) : ℤ) - ((d : ℕ) : ℤ)) =
        ((a : ℕ) : ℤ) - ((d : ℕ) : ℤ) := by ring
    rw [charFn_mul_charFn_inter, hexp]
    congr 2
    refine charFn_congr _ _ ?_
    rw [hset, Set.image_inter (T ^ (((a : ℕ) : ℤ) - m)).injective]
  · have hdisj : Disjoint (⇑(T ^ (((a : ℕ) : ℤ) - m)) '' W)
        (⇑(T ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) '' (⇑(T ^ (((c : ℕ) : ℤ) - m)) '' W')) := by
      have h0 := hlev b c hbc
      have h1 : Disjoint (⇑(T ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) '' (⇑(T ^ (((b : ℕ) : ℤ) - m)) '' U))
          (⇑(T ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) '' (⇑(T ^ (((c : ℕ) : ℤ) - m)) '' U)) :=
        (Set.disjoint_image_iff (T ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))).injective).2 h0
      rw [image_zpow_image_zpow T _ _ U] at h1
      have hab : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) + (((b : ℕ) : ℤ) - m) = ((a : ℕ) : ℤ) - m := by ring
      rw [hab] at h1
      exact h1.mono (Set.image_mono hWU) (Set.image_mono (Set.image_mono hW'U))
    rw [charFn_mul_charFn_of_disjoint k _ _ hdisj, map_zero, zero_mul]

/-- **`E_{ab}(W) ≠ 0`** for nonempty `W` over a nontrivial ring. -/
theorem towerE_ne_zero [Nontrivial k] {m : ℕ} {W : Set X} (hW : IsClopen W) (hne : W.Nonempty)
    (a b : Fin (2 * m + 1)) : towerE T k m hW a b ≠ 0 := by
  intro h
  have h2 : coeff T k (LocallyConstant.charFn k (isClopen_image (T ^ (((a : ℕ) : ℤ) - m)) hW)) = 0 := by
    have h3 := congrArg (· * (((unit T k ^ (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)))⁻¹ :
      (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) h
    simpa only [towerE, mul_assoc, Units.mul_inv, mul_one, zero_mul] using h3
  rw [coeff_apply, Pestov91.CrossedProduct.C_apply, SkewMonoidAlgebra.single_eq_zero,
    RingEquiv.map_eq_zero_iff] at h2
  obtain ⟨x, hx⟩ := hne
  have h4 := LocallyConstant.congr_fun h2 ((T ^ (((a : ℕ) : ℤ) - m)) x)
  rw [LocallyConstant.zero_apply, LocallyConstant.charFn_eq_zero] at h4
  exact h4 ⟨x, hx, rfl⟩

/-- The unit `∑_a E_{aa}(W)` of the tower over `W`. -/
noncomputable def levelSum (m : ℕ) {W : Set X} (hW : IsClopen W) : ClopenCrossedProduct T k :=
  ∑ a : Fin (2 * m + 1), towerE T k m hW a a

theorem levelSum_mul_towerE {m : ℕ} {U W W' : Set X} (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U)
    (hW'U : W' ⊆ U) (hW : IsClopen W) (hW' : IsClopen W') (c d : Fin (2 * m + 1)) :
    levelSum (T := T) (k := k) m hW * towerE T k m hW' c d = towerE T k m (hW.inter hW') c d := by
  rw [levelSum, Finset.sum_mul]
  simp only [towerE_mul_towerE hlev hWU hW'U hW hW', Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem towerE_mul_levelSum {m : ℕ} {U W W' : Set X} (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U)
    (hW'U : W' ⊆ U) (hW : IsClopen W) (hW' : IsClopen W') (c d : Fin (2 * m + 1)) :
    towerE T k m hW' c d * levelSum (T := T) (k := k) m hW = towerE T k m (hW.inter hW') c d := by
  rw [levelSum, Finset.mul_sum]
  simp only [towerE_mul_towerE hlev hW'U hWU hW' hW, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold towerE
  congr 2
  exact charFn_congr _ _ (by rw [Set.inter_comm])

/-- **The tower unit over `W` commutes with `B_m(U)`.** -/
theorem levelSum_mul_eq_mul_levelSum {m : ℕ} {U W : Set X} (hlev : LevelsDisjoint T m U)
    (hWU : W ⊆ U) (hW : IsClopen W) {x : ClopenCrossedProduct T k} (hx : x ∈ towerSpan T k m U) :
    levelSum (T := T) (k := k) m hW * x = x * levelSum (T := T) (k := k) m hW := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨W', hW', hW'U, c, d, rfl⟩ := hy
    rw [levelSum_mul_towerE hlev hWU hW'U hW hW', towerE_mul_levelSum hlev hWU hW'U hW hW']
  | zero => rw [mul_zero, zero_mul]
  | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz]
  | neg y _ hy => rw [mul_neg, neg_mul, hy]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerE_mul_towerE
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerE_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.levelSum_mul_eq_mul_levelSum

end SimpleKazhdanSofic
end GroupApproximation
