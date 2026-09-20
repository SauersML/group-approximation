import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.AltConsecutive
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Cylinders
import GroupApproximation.Meta.AxiomGuard

/-!
# Growing cylinders: the alternating groups on long cylinders

Let `S` be an infinite minimal subshift with shift `T`, let `R` be a radius with `SepRadius S p R`
(`p ≥ 5`) and `N = 2R + 1`. Say a clopen set `B` is `Good` for a subgroup `G` if every even
permutation of the five-level tower over `B` acts, as a tower action, by an element of `G`.

* `good_step`: if `cyl z a c` and `cyl (z (1 + ·)) a c` are good, so are `cyl z a (c + 1)` and
  `cyl (z (1 + ·)) (a - 1) c`. The second cylinder is level `1` of the six-level tower over the
  first, and both are intersections as in `commutator_towerPerm_localize`. Each consecutive
  three-cycle on the target is a single commutator of three-cycles on `U` and `V`
  (`mem_of_witness`, with the witnesses checked by `decide`).
* `good_right`, `good_left`: so if the cylinders on the window `[0, N]` are good, every cylinder on
  a window `[a, b]` with `a ≤ 0` and `b ≥ N` is good (grow to the right, then to the left).
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift Equiv
open scoped commutatorElement

variable {X : Type*}

theorem commutatorElement_mem {G : Subgroup (Perm X)} {g h : Perm X} (hg : g ∈ G) (hh : h ∈ G) :
    ⁅g, h⁆ ∈ G := by
  rw [commutatorElement_def]
  exact G.mul_mem (G.mul_mem (G.mul_mem hg hh) (G.inv_mem hg)) (G.inv_mem hh)

/-- The three-cycle `a ↦ b ↦ c ↦ a`. -/
def cyc {n : ℕ} (a b c : Fin n) : Perm (Fin n) := swap a c * swap a b

theorem cyc_mem_alternatingGroup {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    cyc a b c ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, cyc, Perm.sign_mul, Perm.sign_swap hac, Perm.sign_swap hab]
  exact Int.units_mul_self _

/-- **One consecutive three-cycle from one commutator.** -/
theorem mem_of_witness {G : Subgroup (Perm X)} {f₀ : Perm X} {U V W B : Set X}
    (hU5 : SepK f₀ U 5) (hV5 : SepK f₀ V 5)
    (hUV : ∀ x ∈ U, ∀ d : ℤ, -4 ≤ d → d ≤ 4 → d ≠ 1 → (f₀ ^ d) x ∉ V)
    (hWd : ∀ x, x ∈ W ↔ x ∈ U ∧ f₀ x ∈ V)
    (hU : TowerDisj f₀ U 4) (hV : TowerDisj f₀ V 4) (hW : TowerDisj f₀ W 5)
    (hGU : ∀ σ ∈ alternatingGroup (Fin 5), towerPerm f₀ U (towerLevels 4) hU σ ∈ G)
    (hGV : ∀ σ ∈ alternatingGroup (Fin 5), towerPerm f₀ V (towerLevels 4) hV σ ∈ G)
    (hB : TowerDisj f₀ B 4) (e : Fin 5 → Fin 6) (c : ℤ)
    (hE : ∀ i, towerLevels 5 (e i) = towerLevels 4 i + c) (hBW : ∀ x, x ∈ W ↔ (f₀ ^ c) x ∈ B)
    (τ α β : Perm (Fin 5)) (α' β' : Perm (Fin 6))
    (hα : ∀ i : Fin 5, α' i.castSucc = (α i).castSucc) (hα5 : α' (Fin.last 5) = Fin.last 5)
    (hβ : ∀ i : Fin 5, β' i.succ = (β i).succ) (hβ0 : β' 0 = 0)
    (hαA : α ∈ alternatingGroup (Fin 5)) (hβA : β ∈ alternatingGroup (Fin 5))
    (h1 : ∀ i, ⁅α', β'⁆ (e i) = e (τ i)) (h2 : ∀ j, (∀ i, e i ≠ j) → ⁅α', β'⁆ j = j) :
    towerPerm f₀ B (towerLevels 4) hB τ ∈ G := by
  rw [towerPerm_eq_of_sub hB hW e c hE hBW τ ⁅α', β'⁆ h1 h2,
    ← commutator_towerPerm_localize hU5 hV5 hUV hWd hU hV hW α β α' β' hα hα5 hβ hβ0]
  exact commutatorElement_mem (hGU α hαA) (hGV β hβA)

/-- The three consecutive three-cycles of `Fin 5`. -/
theorem consSet_four_cases {P : Perm (Fin 5) → Prop}
    (h0 : P (adjSwap (⟨0, by norm_num⟩ : Fin 4) * adjSwap (⟨1, by norm_num⟩ : Fin 4)))
    (h1 : P (adjSwap (⟨1, by norm_num⟩ : Fin 4) * adjSwap (⟨2, by norm_num⟩ : Fin 4)))
    (h2 : P (adjSwap (⟨2, by norm_num⟩ : Fin 4) * adjSwap (⟨3, by norm_num⟩ : Fin 4))) :
    ∀ τ ∈ consSet 4, P τ := by
  rintro τ ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, rfl⟩
  simp only at hij
  subst hij
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact absurd hj (by norm_num)

section Subshift

variable {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)

/-- Every even permutation of the five-level tower over `B` acts by an element of `G`. -/
def Good (G : Subgroup (Perm S.carrier)) (B : Set S.carrier) : Prop :=
  ∀ h : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B 4,
    ∀ σ ∈ alternatingGroup (Fin 5),
      towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B (towerLevels 4) h σ ∈ G

theorem good_of_cons {G : Subgroup (Perm S.carrier)} {B : Set S.carrier}
    (hc : ∀ h : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B 4, ∀ σ ∈ consSet 4,
      towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B (towerLevels 4) h σ ∈ G) :
    Good S G B := by
  intro h σ hσ
  have hle : Subgroup.closure (consSet 4) ≤
      G.comap (towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B (towerLevels 4) h) := by
    rw [Subgroup.closure_le]
    intro τ hτ
    exact hc h τ hτ
  exact hle (alternatingGroup_le_closure_consSet 4 (by norm_num) hσ)

/-- **One step**: two good cylinders on `[a, c]` give good cylinders on `[a, c + 1]` and on
`[a - 1, c]`. -/
theorem good_step {G : Subgroup (Perm S.carrier)} {p R : ℕ} (hR : SepRadius S p R) (hp : 5 ≤ p)
    {z : ℤ → A} {a c : ℤ} (hac : a + 1 + 2 * (R : ℤ) ≤ c)
    (hU : Good S G (cyl S z a c)) (hV : Good S G (cyl S (fun n => z (1 + n)) a c)) :
    Good S G (cyl S z a (c + 1)) ∧ Good S G (cyl S (fun n => z (1 + n)) (a - 1) c) := by
  have hR5 : SepRadius S 5 R := hR.mono S hp
  have hU5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z a c) 5 :=
    cyl_sepK S hR5 (by omega)
  have hV5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
      (cyl S (fun n => z (1 + n)) a c) 5 := cyl_sepK S hR5 (by omega)
  have hW5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z a (c + 1)) 5 :=
    cyl_sepK S hR5 (by omega)
  have hUV := cyl_cross S hR hp (z := z) hac
  have hWd := mem_cyl_succ_iff S (z := z) (show a ≤ c by omega)
  have hUd : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z a c) 4 :=
    towerDisj_of_sepK (hU5.mono (by norm_num))
  have hVd : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
      (cyl S (fun n => z (1 + n)) a c) 4 := towerDisj_of_sepK (hV5.mono (by norm_num))
  have hWd6 : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z a (c + 1)) 5 :=
    towerDisj_of_sepK hW5
  have hGU := hU hUd
  have hGV := hV hVd
  have hE0 : ∀ i : Fin 5, towerLevels 5 i.castSucc = towerLevels 4 i + 0 := fun i => by
    rw [towerLevels_val, towerLevels_val, Fin.val_castSucc, add_zero]
  have hB0 : ∀ x, x ∈ cyl S z a (c + 1) ↔
      ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ (0 : ℤ)) x ∈ cyl S z a (c + 1) :=
    fun x => by rw [zpow_zero, Equiv.Perm.one_apply]
  have hE1 : ∀ i : Fin 5, towerLevels 5 i.succ = towerLevels 4 i + 1 := fun i => by
    rw [towerLevels_val, towerLevels_val, Fin.val_succ, Nat.cast_succ]
  constructor
  · refine good_of_cons S fun hB => consSet_four_cases ?_ ?_ ?_
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.castSucc 0 hE0 hB0
        _ (cyc 0 3 2) (cyc 1 0 3) (cyc 0 3 2) (cyc 2 1 4)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.castSucc 0 hE0 hB0
        _ (cyc 1 0 3) (cyc 2 1 3) (cyc 1 0 3) (cyc 3 2 4)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.castSucc 0 hE0 hB0
        _ (cyc 2 0 4) (cyc 3 2 4) (cyc 2 0 4) (cyc 4 3 5)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)
  · refine good_of_cons S fun hB => consSet_four_cases ?_ ?_ ?_
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.succ 1 hE1
        (mem_cyl_iff_zpow_one S)
        _ (cyc 1 0 3) (cyc 2 1 3) (cyc 1 0 3) (cyc 3 2 4)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.succ 1 hE1
        (mem_cyl_iff_zpow_one S)
        _ (cyc 2 0 4) (cyc 3 2 4) (cyc 2 0 4) (cyc 4 3 5)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)
    · exact mem_of_witness hU5 hV5 hUV hWd hUd hVd hWd6 hGU hGV hB Fin.succ 1 hE1
        (mem_cyl_iff_zpow_one S)
        _ (cyc 4 0 3) (cyc 2 4 0) (cyc 4 0 3) (cyc 3 5 1)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (cyc_mem_alternatingGroup (by decide) (by decide))
        (by decide +kernel) (by decide +kernel)

/-- **Growing to the right**. -/
theorem good_right {G : Subgroup (Perm S.carrier)} {p R N : ℕ} (hR : SepRadius S p R)
    (hp : 5 ≤ p) (hN : 2 * R + 1 ≤ N) (hbase : ∀ z : ℤ → A, Good S G (cyl S z 0 N)) :
    ∀ k : ℕ, ∀ z : ℤ → A, Good S G (cyl S z 0 ((N : ℤ) + k)) := by
  intro k
  induction k with
  | zero =>
    intro z
    rw [Nat.cast_zero, add_zero]
    exact hbase z
  | succ k ih =>
    intro z
    rw [Nat.cast_succ, ← add_assoc]
    exact (good_step S hR hp (a := 0) (c := (N : ℤ) + k) (by omega) (ih z) (ih _)).1

/-- **Growing to the left**. -/
theorem good_left {G : Subgroup (Perm S.carrier)} {p R N : ℕ} (hR : SepRadius S p R)
    (hp : 5 ≤ p) (hN : 2 * R + 1 ≤ N)
    (hright : ∀ k : ℕ, ∀ z : ℤ → A, Good S G (cyl S z 0 ((N : ℤ) + k))) :
    ∀ j : ℕ, ∀ z : ℤ → A, ∀ b : ℤ, (N : ℤ) ≤ b → Good S G (cyl S z (-(j : ℤ)) b) := by
  intro j
  induction j with
  | zero =>
    intro z b hb
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = (N : ℤ) + k := ⟨(b - N).toNat, by omega⟩
    rw [Nat.cast_zero, neg_zero]
    exact hright k z
  | succ j ih =>
    intro z b hb
    have hz : ∀ n, (fun n => z (-1 + n)) (1 + n) = z n := fun n => by
      show z (-1 + (1 + n)) = z n
      exact congrArg z (by ring)
    have hV : Good S G (cyl S (fun n => (fun n => z (-1 + n)) (1 + n)) (-(j : ℤ)) b) := by
      convert ih z b hb using 2
      all_goals exact funext hz
    have hstep := (good_step S hR hp (z := fun n => z (-1 + n)) (a := -(j : ℤ)) (c := b)
      (by omega) (ih _ b hb) hV).2
    convert hstep using 2
    all_goals first | exact funext hz | exact (funext hz).symm | (push_cast; ring)

end Subshift

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.good_step
#audit_axioms GroupApproximation.Full.SKTFG.good_left
