import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiLevelSwaps
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower actions: sub-towers and localization of commutators

Tools for the finite generation of the derived topological full group of a minimal subshift
(`SKTFG.FG`), for a permutation `f₀` of a set `X` (the shift) and the tower actions `towerPerm`
of `Full.StepanovMatui.Matui`.

* `towerPerm_eq_of_sub`: a tower action on a sub-tower equals the tower action on the big tower
  of the extended permutation (`σ'` extends `σ` along the level map `e`, and is the identity off
  the image of `e`).
* `commutator_towerPerm_localize`: let `U, V` be bases of five-level towers and
  `W = {x ∈ U | f₀ x ∈ V}`. If the `U`-tower and the `V`-tower meet only along the levels
  `1, …, 5` of `W` (hypothesis `hUV`), then the commutator of a tower action over `U` and a
  tower action over `V` is the tower action over `W` of the commutator of the extended
  permutations of the six levels of `W`. So commutators localize tower actions to
  intersections.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.Full.StepanovMatui.Matui
open scoped commutatorElement

variable {X : Type*}

/-- The levels `0, …, K` of the tower over `B` along `f₀` are pairwise disjoint. -/
abbrev TowerDisj (f₀ : Equiv.Perm X) (B : Set X) (K : ℕ) : Prop :=
  ∀ i j : Fin (K + 1), ∀ x, (f₀ ^ (-towerLevels K i)) x ∈ B →
    (f₀ ^ (-towerLevels K j)) x ∈ B → i = j

/-- No point of `B` returns to `B` within `K` steps of `f₀`. -/
def SepK (f₀ : Equiv.Perm X) (B : Set X) (K : ℕ) : Prop :=
  ∀ x ∈ B, ∀ d : ℤ, d ≠ 0 → -(K : ℤ) ≤ d → d ≤ K → (f₀ ^ d) x ∉ B

theorem towerLevels_val (K : ℕ) (i : Fin (K + 1)) : towerLevels K i = ((i : ℕ) : ℤ) := rfl

theorem SepK.mono {f₀ : Equiv.Perm X} {B : Set X} {K L : ℕ} (h : SepK f₀ B K) (hLK : L ≤ K) :
    SepK f₀ B L := fun x hx d hd h1 h2 => h x hx d hd (by omega) (by omega)

theorem towerDisj_of_sepK {f₀ : Equiv.Perm X} {B : Set X} {K : ℕ} (h : SepK f₀ B K) :
    TowerDisj f₀ B K := by
  intro i j x hi hj
  by_contra hij
  have hne : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≠ 0 := by
    intro h0
    exact hij (Fin.ext (by omega))
  have hi' := i.isLt
  have hj' := j.isLt
  refine h _ hj (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) hne (by omega) (by omega) ?_
  rw [perm_zpow_apply_zpow_apply]
  have e : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) + -towerLevels K j = -towerLevels K i := by
    rw [towerLevels_val, towerLevels_val]
    ring
  rw [e]
  exact hi

theorem perm_apply_inv_self' (f₀ : Equiv.Perm X) (x : X) : f₀ (f₀⁻¹ x) = x :=
  Equiv.apply_symm_apply f₀ x

theorem perm_zpow_congr (f₀ : Equiv.Perm X) {a b : ℤ} (h : a = b) (x : X) :
    (f₀ ^ a) x = (f₀ ^ b) x := by
  rw [h]

/-! ## Sub-towers -/

/-- **Sub-towers.** Let the levels of the small tower be `f₀ ^ E i` over `B`, and the levels of
the big tower be `f₀ ^ E' j` over `B'`, with `E' (e i) = E i + c` and `B' = f₀^{-c} B`. If `σ'`
extends `σ` along `e` and fixes the other levels, the two tower actions agree. -/
theorem towerPerm_eq_of_sub {f₀ : Equiv.Perm X} {B B' : Set X} {n n' : ℕ} {E : Fin n → ℤ}
    {E' : Fin n' → ℤ}
    (hd : ∀ i j x, (f₀ ^ (-E i)) x ∈ B → (f₀ ^ (-E j)) x ∈ B → i = j)
    (hd' : ∀ i j x, (f₀ ^ (-E' i)) x ∈ B' → (f₀ ^ (-E' j)) x ∈ B' → i = j)
    (e : Fin n → Fin n') (c : ℤ) (hE : ∀ i, E' (e i) = E i + c)
    (hB : ∀ x, x ∈ B' ↔ (f₀ ^ c) x ∈ B)
    (σ : Equiv.Perm (Fin n)) (σ' : Equiv.Perm (Fin n'))
    (h1 : ∀ i, σ' (e i) = e (σ i)) (h2 : ∀ j, (∀ i, e i ≠ j) → σ' j = j) :
    towerPerm f₀ B E hd σ = towerPerm f₀ B' E' hd' σ' := by
  refine Equiv.ext fun x => ?_
  rw [towerPerm_apply, towerPerm_apply]
  by_cases h : ∃ i, (f₀ ^ (-E i)) x ∈ B
  · obtain ⟨i, hi⟩ := h
    have hi' : (f₀ ^ (-E' (e i))) x ∈ B' := by
      rw [hB, perm_zpow_apply_zpow_apply, hE,
        show c + -(E i + c) = -E i by ring]
      exact hi
    rw [towerFun_of_mem hd hi, towerFun_of_mem hd' hi', h1, hE, hE]
    exact perm_zpow_congr f₀ (by ring) x
  · rw [towerFun_of_not h]
    by_cases h' : ∃ j, (f₀ ^ (-E' j)) x ∈ B'
    · obtain ⟨j, hj⟩ := h'
      have hj' : ∀ i, e i ≠ j := by
        rintro i rfl
        apply h
        refine ⟨i, ?_⟩
        have hB' := (hB _).mp hj
        rwa [perm_zpow_apply_zpow_apply, hE, show c + -(E i + c) = -E i by ring] at hB'
      rw [towerFun_of_mem hd' hj, h2 j hj', sub_self, zpow_zero, Equiv.Perm.one_apply]
    · rw [towerFun_of_not h']

/-! ## Localizing commutators of tower actions -/

section Localize

variable {f₀ : Equiv.Perm X} {U V W : Set X}

/-- **Commutators localize tower actions.** -/
theorem commutator_towerPerm_localize
    (hU5 : SepK f₀ U 5) (hV5 : SepK f₀ V 5)
    (hUV : ∀ x ∈ U, ∀ d : ℤ, -4 ≤ d → d ≤ 4 → d ≠ 1 → (f₀ ^ d) x ∉ V)
    (hWd : ∀ x, x ∈ W ↔ x ∈ U ∧ f₀ x ∈ V)
    (hU : TowerDisj f₀ U 4) (hV : TowerDisj f₀ V 4) (hW : TowerDisj f₀ W 5)
    (α β : Equiv.Perm (Fin 5)) (α' β' : Equiv.Perm (Fin 6))
    (hα : ∀ i : Fin 5, α' i.castSucc = (α i).castSucc) (hα5 : α' (Fin.last 5) = Fin.last 5)
    (hβ : ∀ i : Fin 5, β' i.succ = (β i).succ) (hβ0 : β' 0 = 0) :
    ⁅towerPerm f₀ U (towerLevels 4) hU α, towerPerm f₀ V (towerLevels 4) hV β⁆ =
      towerPerm f₀ W (towerLevels 5) hW ⁅α', β'⁆ := by
  set a := towerPerm f₀ U (towerLevels 4) hU α with ha
  set b := towerPerm f₀ V (towerLevels 4) hV β with hb
  have hWU : ∀ w ∈ W, w ∈ U := fun w hw => ((hWd w).mp hw).1
  have hWV : ∀ w ∈ W, f₀ w ∈ V := fun w hw => ((hWd w).mp hw).2
  -- `a` acts on the `W`-tower as `α'`
  have ha_tow : ∀ w ∈ W, ∀ k : Fin 6,
      a ((f₀ ^ ((k : ℕ) : ℤ)) w) = (f₀ ^ (((α' k : Fin 6) : ℕ) : ℤ)) w := by
    intro w hw k
    have hk6 := k.isLt
    by_cases hk : (k : ℕ) ≤ 4
    · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, k = i.castSucc := ⟨⟨k, by omega⟩, Fin.ext rfl⟩
      have hlev : (f₀ ^ (-towerLevels 4 i)) ((f₀ ^ (((i.castSucc : Fin 6) : ℕ) : ℤ)) w) ∈ U := by
        rw [perm_zpow_apply_zpow_apply, towerLevels_val, Fin.val_castSucc, neg_add_cancel,
          zpow_zero, Equiv.Perm.one_apply]
        exact hWU w hw
      rw [ha, towerPerm_apply, towerFun_of_mem hU hlev, perm_zpow_apply_zpow_apply, hα]
      refine perm_zpow_congr f₀ ?_ w
      rw [towerLevels_val, towerLevels_val, Fin.val_castSucc, Fin.val_castSucc]
      ring
    · obtain rfl : k = Fin.last 5 := Fin.ext (by rw [Fin.val_last]; omega)
      have hnot : ¬∃ j : Fin 5,
          (f₀ ^ (-towerLevels 4 j)) ((f₀ ^ ((((Fin.last 5) : Fin 6) : ℕ) : ℤ)) w) ∈ U := by
        rintro ⟨j, hj⟩
        rw [perm_zpow_apply_zpow_apply, towerLevels_val, Fin.val_last] at hj
        have hj5 := j.isLt
        exact hU5 w (hWU w hw) (-((j : ℕ) : ℤ) + ((5 : ℕ) : ℤ)) (by omega) (by omega) (by omega) hj
      rw [ha, towerPerm_apply, towerFun_of_not hnot, hα5]
  -- `b` acts on the `W`-tower as `β'`
  have hb_tow : ∀ w ∈ W, ∀ k : Fin 6,
      b ((f₀ ^ ((k : ℕ) : ℤ)) w) = (f₀ ^ (((β' k : Fin 6) : ℕ) : ℤ)) w := by
    intro w hw k
    have hk6 := k.isLt
    by_cases hk : 1 ≤ (k : ℕ)
    · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, k = i.succ :=
        ⟨⟨(k : ℕ) - 1, by omega⟩, Fin.ext (by rw [Fin.val_succ]; show (k : ℕ) = (k : ℕ) - 1 + 1; omega)⟩
      have hlev : (f₀ ^ (-towerLevels 4 i)) ((f₀ ^ (((i.succ : Fin 6) : ℕ) : ℤ)) w) ∈ V := by
        rw [perm_zpow_apply_zpow_apply, towerLevels_val, Fin.val_succ,
          show -((i : ℕ) : ℤ) + (((i : ℕ) + 1 : ℕ) : ℤ) = 1 by push_cast; ring, zpow_one]
        exact hWV w hw
      rw [hb, towerPerm_apply, towerFun_of_mem hV hlev, perm_zpow_apply_zpow_apply, hβ]
      refine perm_zpow_congr f₀ ?_ w
      rw [towerLevels_val, towerLevels_val, Fin.val_succ, Fin.val_succ]
      push_cast
      ring
    · obtain rfl : k = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      have hnot : ¬∃ j : Fin 5,
          (f₀ ^ (-towerLevels 4 j)) ((f₀ ^ ((((0 : Fin 6)) : ℕ) : ℤ)) w) ∈ V := by
        rintro ⟨j, hj⟩
        rw [perm_zpow_apply_zpow_apply, towerLevels_val, Fin.val_zero] at hj
        have hj5 := j.isLt
        refine hV5 _ hj (1 + ((j : ℕ) : ℤ)) (by omega) (by omega) (by omega) ?_
        rw [perm_zpow_apply_zpow_apply,
          show 1 + ((j : ℕ) : ℤ) + (-((j : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) = 1 by push_cast; ring,
          zpow_one]
        exact hWV w hw
      rw [hb, towerPerm_apply, towerFun_of_not hnot, hβ0]
  -- inverses on the `W`-tower
  have ha_inv : ∀ w ∈ W, ∀ k : Fin 6,
      a⁻¹ ((f₀ ^ ((k : ℕ) : ℤ)) w) = (f₀ ^ (((α'⁻¹ k : Fin 6) : ℕ) : ℤ)) w := by
    intro w hw k
    have h := ha_tow w hw (α'⁻¹ k)
    rw [perm_apply_inv_self'] at h
    rw [← h, perm_inv_apply_self]
  have hb_inv : ∀ w ∈ W, ∀ k : Fin 6,
      b⁻¹ ((f₀ ^ ((k : ℕ) : ℤ)) w) = (f₀ ^ (((β'⁻¹ k : Fin 6) : ℕ) : ℤ)) w := by
    intro w hw k
    have h := hb_tow w hw (β'⁻¹ k)
    rw [perm_apply_inv_self'] at h
    rw [← h, perm_inv_apply_self]
  -- the commutator on the `W`-tower
  have hcomm_tow : ∀ w ∈ W, ∀ k : Fin 6,
      ⁅a, b⁆ ((f₀ ^ ((k : ℕ) : ℤ)) w) = (f₀ ^ (((⁅α', β'⁆ k : Fin 6) : ℕ) : ℤ)) w := by
    intro w hw k
    simp only [commutatorElement_def, Equiv.Perm.mul_apply]
    rw [hb_inv w hw, ha_inv w hw, hb_tow w hw, ha_tow w hw]
  -- the inverses as tower actions
  have ha_inv_def : a⁻¹ = towerPerm f₀ U (towerLevels 4) hU α⁻¹ := by rw [ha, map_inv]
  have hb_inv_def : b⁻¹ = towerPerm f₀ V (towerLevels 4) hV β⁻¹ := by rw [hb, map_inv]
  -- off the `W`-tower the commutator is trivial
  have hoff : ∀ x, (¬∃ k : Fin 6, (f₀ ^ (-towerLevels 5 k)) x ∈ W) → ⁅a, b⁆ x = x := by
    intro x hx
    simp only [commutatorElement_def, Equiv.Perm.mul_apply]
    by_cases hxU : ∃ i : Fin 5, (f₀ ^ (-towerLevels 4 i)) x ∈ U
    · obtain ⟨i, hi⟩ := hxU
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, x = (f₀ ^ towerLevels 4 i) u :=
        ⟨_, hi, by rw [perm_zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
          Equiv.Perm.one_apply]⟩
      have hfu : f₀ u ∉ V := by
        intro hfu
        apply hx
        refine ⟨i.castSucc, (hWd _).mpr ⟨?_, ?_⟩⟩
        · rw [perm_zpow_apply_zpow_apply, towerLevels_val, towerLevels_val, Fin.val_castSucc,
            neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
          exact hu
        · rw [perm_zpow_apply_zpow_apply, towerLevels_val, towerLevels_val, Fin.val_castSucc,
            neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
          exact hfu
      have hB1 : ∀ j : Fin 5, ¬∃ l : Fin 5,
          (f₀ ^ (-towerLevels 4 l)) ((f₀ ^ towerLevels 4 j) u) ∈ V := by
        rintro j ⟨l, hl⟩
        rw [perm_zpow_apply_zpow_apply] at hl
        have hl5 := l.isLt
        have hj5 := j.isLt
        by_cases hd1 : -towerLevels 4 l + towerLevels 4 j = 1
        · rw [hd1, zpow_one] at hl
          exact hfu hl
        · refine hUV u hu _ ?_ ?_ hd1 hl
          · rw [towerLevels_val, towerLevels_val]; omega
          · rw [towerLevels_val, towerLevels_val]; omega
      have hbinv : b⁻¹ ((f₀ ^ towerLevels 4 i) u) = (f₀ ^ towerLevels 4 i) u := by
        rw [hb_inv_def, towerPerm_apply, towerFun_of_not (hB1 i)]
      have hainv : a⁻¹ ((f₀ ^ towerLevels 4 i) u) = (f₀ ^ towerLevels 4 (α⁻¹ i)) u := by
        rw [ha_inv_def, towerPerm_apply, towerFun_of_mem hU hi, perm_zpow_apply_zpow_apply,
          sub_add_cancel]
      have hbfix : b ((f₀ ^ towerLevels 4 (α⁻¹ i)) u) = (f₀ ^ towerLevels 4 (α⁻¹ i)) u := by
        rw [hb, towerPerm_apply, towerFun_of_not (hB1 (α⁻¹ i))]
      rw [hbinv, hainv, hbfix, ← hainv, perm_apply_inv_self']
    · by_cases hxV : ∃ i : Fin 5, (f₀ ^ (-towerLevels 4 i)) x ∈ V
      · obtain ⟨i, hi⟩ := hxV
        have hax : a x = x := by rw [ha, towerPerm_apply, towerFun_of_not hxU]
        obtain ⟨v, hv, rfl⟩ : ∃ v ∈ V, x = (f₀ ^ towerLevels 4 i) v :=
          ⟨_, hi, by rw [perm_zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
            Equiv.Perm.one_apply]⟩
        have hfv : (f₀ ^ (-1 : ℤ)) v ∉ U := by
          intro hfv
          apply hx
          refine ⟨i.succ, (hWd _).mpr ⟨?_, ?_⟩⟩
          · rw [perm_zpow_apply_zpow_apply, towerLevels_val, towerLevels_val, Fin.val_succ,
              show -((((i : ℕ) + 1 : ℕ)) : ℤ) + ((i : ℕ) : ℤ) = -1 by push_cast; ring]
            exact hfv
          · rw [perm_zpow_apply_zpow_apply, towerLevels_val, towerLevels_val, Fin.val_succ,
              show -((((i : ℕ) + 1 : ℕ)) : ℤ) + ((i : ℕ) : ℤ) = -1 by push_cast; ring]
            have e : f₀ ((f₀ ^ (-1 : ℤ)) v) = v := by
              rw [zpow_neg_one, perm_apply_inv_self']
            rw [e]
            exact hv
        have hB2 : ∀ j : Fin 5, ¬∃ l : Fin 5,
            (f₀ ^ (-towerLevels 4 l)) ((f₀ ^ towerLevels 4 j) v) ∈ U := by
          rintro j ⟨l, hl⟩
          rw [perm_zpow_apply_zpow_apply] at hl
          have hl5 := l.isLt
          have hj5 := j.isLt
          have hback : (f₀ ^ (towerLevels 4 l - towerLevels 4 j))
              ((f₀ ^ (-towerLevels 4 l + towerLevels 4 j)) v) = v := by
            rw [perm_zpow_apply_zpow_apply,
              show towerLevels 4 l - towerLevels 4 j + (-towerLevels 4 l + towerLevels 4 j) = 0
                by ring, zpow_zero, Equiv.Perm.one_apply]
          by_cases hd1 : towerLevels 4 l - towerLevels 4 j = 1
          · rw [hd1, zpow_one] at hback
            apply hfv
            rw [← hback, zpow_neg_one, perm_inv_apply_self]
            exact hl
          · refine hUV _ hl _ ?_ ?_ hd1 ?_
            · rw [towerLevels_val, towerLevels_val]; omega
            · rw [towerLevels_val, towerLevels_val]; omega
            · rw [hback]
              exact hv
        have hbinv : b⁻¹ ((f₀ ^ towerLevels 4 i) v) = (f₀ ^ towerLevels 4 (β⁻¹ i)) v := by
          rw [hb_inv_def, towerPerm_apply, towerFun_of_mem hV hi, perm_zpow_apply_zpow_apply,
            sub_add_cancel]
        have hafix : a⁻¹ ((f₀ ^ towerLevels 4 (β⁻¹ i)) v) = (f₀ ^ towerLevels 4 (β⁻¹ i)) v := by
          rw [ha_inv_def, towerPerm_apply, towerFun_of_not (hB2 (β⁻¹ i))]
        rw [hbinv, hafix, ← hbinv, perm_apply_inv_self', hax]
      · have hax : ∀ σ : Equiv.Perm (Fin 5), towerPerm f₀ U (towerLevels 4) hU σ x = x :=
          fun σ => by rw [towerPerm_apply, towerFun_of_not hxU]
        have hbx : ∀ σ : Equiv.Perm (Fin 5), towerPerm f₀ V (towerLevels 4) hV σ x = x :=
          fun σ => by rw [towerPerm_apply, towerFun_of_not hxV]
        rw [hb_inv_def, hbx, ha_inv_def, hax, hb, hbx, ha, hax]
  -- assemble
  refine Equiv.ext fun x => ?_
  by_cases hx : ∃ k : Fin 6, (f₀ ^ (-towerLevels 5 k)) x ∈ W
  · obtain ⟨k, hk⟩ := hx
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, x = (f₀ ^ ((k : ℕ) : ℤ)) w :=
      ⟨_, hk, by rw [perm_zpow_apply_zpow_apply, towerLevels_val, add_neg_cancel, zpow_zero,
        Equiv.Perm.one_apply]⟩
    rw [hcomm_tow w hw k, towerPerm_apply, towerFun_of_mem hW hk, perm_zpow_apply_zpow_apply]
    refine perm_zpow_congr f₀ ?_ w
    rw [towerLevels_val, towerLevels_val]
    ring
  · rw [hoff x hx, towerPerm_apply, towerFun_of_not hx]

end Localize

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.towerPerm_eq_of_sub
#audit_axioms GroupApproximation.Full.SKTFG.commutator_towerPerm_localize
