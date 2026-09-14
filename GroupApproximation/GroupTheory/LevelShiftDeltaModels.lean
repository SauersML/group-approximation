import GroupApproximation.GroupTheory.LevelShiftDelta
import GroupApproximation.GroupTheory.ShiftTransversalBijection
import GroupApproximation.Sofic.LEF
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The finite models of the second choice of `Δ`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, section "LEF groups", tex l.377–382:

> As f is trivial below −r and constant from r on, ζ^ℓ(ψ(f(m)))_m ζ^{−ℓ} = (ψ(f(m−ℓ)))_m for |ℓ| ≤ r. So
> fβ^ℓ ↦ (ψ(f(m)))_{|m|≤3r} ζ^ℓ preserves the products that stay in the ball of radius r, and it is injective there, as
> 5r > 2r and f is determined by its values for |m| ≤ 3r. So Δ is LEF, and the rest of the proof applies to it.

The radius is `r = s + 1` and the window is `Fin (6s + 7)`, position `k` standing for the level `k − 3r`.

* `window ψ s F`: the vector `(ψ(F(m)))_{|m| ≤ 3r}`;
* `zeta_zpow_conj`: `ζ^ℓ (window F) ζ^{−ℓ} = window (F(· − ℓ))` for `F` trivial below `−r` and constant from `r` on, and
  `|ℓ| ≤ r`, by iterating `ζ v ζ⁻¹ = θ(v)`;
* `model ψ s L g = (window (levelFunOf g)) ζ^{levelShiftOf g}`, with `model_mul` (products) and `model_injOn` (injectivity,
  using `L > 2r`);
* `isTextbookLEF_levelDelta`: `Δ` is LEF, with `L = 5r`.
-/

namespace GroupApproximation
namespace LevelShiftDelta

open Equiv ShiftTransversalBijection

section Conj

variable {G : Type*} [Group G]

theorem conj_mul_conj (a b x : G) : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  group

theorem conj_inv_mul_conj (a b x : G) : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by
  group

theorem mul_zpow_mul_split (x y a : G) (m n : ℤ) :
    x * a ^ m * (y * a ^ n) = x * (a ^ m * y * (a ^ m)⁻¹) * a ^ (m + n) := by
  rw [zpow_add]
  group

end Conj

section Tame

variable {Γ : Type*} [Group Γ]

/-- `F` is trivial below `lo` and constant from `hi` on. -/
def Tame (F : ℤ → Γ) (lo hi : ℤ) : Prop :=
  (∀ m, m < lo → F m = 1) ∧ ∀ m, hi < m → F m = F hi

theorem Tame.eq_of_le {F : ℤ → Γ} {lo hi : ℤ} (h : Tame F lo hi) {a b : ℤ} (ha : hi ≤ a)
    (hb : hi ≤ b) : F a = F b := by
  have key : ∀ c, hi ≤ c → F c = F hi := fun c hc => by
    rcases lt_or_eq_of_le hc with hlt | heq
    · exact h.2 c hlt
    · rw [heq]
  rw [key a ha, key b hb]

theorem Tame.shift_sub {F : ℤ → Γ} {lo hi : ℤ} (h : Tame F lo hi) (d : ℤ) :
    Tame (fun m => F (m - d)) (lo + d) (hi + d) := by
  refine ⟨fun m hm => h.1 (m - d) (by linarith), fun m hm => ?_⟩
  show F (m - d) = F (hi + d - d)
  rw [h.2 (m - d) (by linarith), show hi + d - d = hi by ring]

theorem Tame.shift_add {F : ℤ → Γ} {lo hi : ℤ} (h : Tame F lo hi) (d : ℤ) :
    Tame (fun m => F (m + d)) (lo - d) (hi - d) := by
  refine ⟨fun m hm => h.1 (m + d) (by linarith), fun m hm => ?_⟩
  show F (m + d) = F (hi - d + d)
  rw [h.2 (m + d) (by linarith), show hi - d + d = hi by ring]

theorem LevelBounds.tame {E : Set Γ} {r : ℕ} {f : ℤ → Γ} {ℓ : ℤ} (h : LevelBounds E r f ℓ) :
    Tame f (-(r : ℤ)) r :=
  ⟨h.2.2.1, h.2.2.2⟩

end Tame

section Window

variable {Γ Q : Type*} [Group Γ] [Group Q] (ψ : Γ → Q) (s : ℕ)

/-- The window `(ψ(F(m)))_{|m| ≤ 3r}` for `r = s + 1`, position `k` standing for the level `k − 3r` (tex l.379). -/
def window (F : ℤ → Γ) : Fin (6 * s + 5 + 2) → Q :=
  fun k => ψ (F ((k : ℕ) - (3 * s + 3 : ℤ)))

theorem window_mem_dom {F : ℤ → Γ} (hF : F (3 * s + 2) = F (3 * s + 3)) :
    window ψ s F ∈ dom Q (6 * s + 5) := by
  rw [mem_dom]
  show ψ (F (((6 * s + 5 : ℕ) : ℤ) - (3 * s + 3))) = ψ (F (((6 * s + 5 + 1 : ℕ) : ℤ) - (3 * s + 3)))
  have h1 : ((6 * s + 5 : ℕ) : ℤ) - (3 * s + 3) = 3 * s + 2 := by push_cast; ring
  have h2 : ((6 * s + 5 + 1 : ℕ) : ℤ) - (3 * s + 3) = 3 * s + 3 := by push_cast; ring
  rw [h1, h2, hF]

/-- `θ` shifts a window by one level when `F` is trivial just below the window. -/
theorem theta_window {F : ℤ → Γ} (hψ : ψ 1 = 1) (hF : F (-(3 * s + 3) - 1) = 1) :
    theta Q (6 * s + 5) (window ψ s F) = window ψ s (fun m => F (m - 1)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    rw [theta_zero]
    show 1 = ψ (F ((((0 : Fin (6 * s + 5 + 2)) : ℕ) : ℤ) - (3 * s + 3) - 1))
    rw [Fin.val_zero, Nat.cast_zero, zero_sub, hF, hψ]
  | succ k =>
    rw [theta_succ]
    show ψ (F ((((Fin.castSucc k : Fin (6 * s + 5 + 2)) : ℕ) : ℤ) - (3 * s + 3))) =
      ψ (F (((((Fin.succ k : Fin (6 * s + 5 + 2)) : ℕ) : ℤ) - (3 * s + 3)) - 1))
    rw [Fin.coe_castSucc, Fin.val_succ]
    congr 2
    push_cast
    ring

variable (L : ℕ) [Finite Q]

/-- Conjugation by `ζ^n` moves the window `n` levels up. -/
theorem zeta_pow_conj (hψ : ψ 1 = 1) :
    ∀ (n : ℕ) {F : ℤ → Γ} {lo hi : ℤ}, Tame F lo hi → -(3 * s + 3 : ℤ) ≤ lo → hi + n ≤ 3 * s + 3 →
      zeta Q (6 * s + 5) L ^ n * lmul Q (6 * s + 5) L (window ψ s F) * (zeta Q (6 * s + 5) L ^ n)⁻¹ =
        lmul Q (6 * s + 5) L (window ψ s fun m => F (m - n))
  | 0, F, _, _, _, _, _ => by simp
  | n + 1, F, lo, hi, hT, hlo, hhi => by
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    push_cast at hhi
    have hdom : window ψ s F ∈ dom Q (6 * s + 5) :=
      window_mem_dom ψ s (hT.eq_of_le (by linarith) (by linarith))
    have hth : theta Q (6 * s + 5) (window ψ s F) = window ψ s fun m => F (m - 1) :=
      theta_window ψ s hψ (hT.1 (-(3 * s + 3) - 1) (by linarith))
    rw [pow_succ, conj_mul_conj, zeta_mul_lmul_mul_zeta_inv Q (6 * s + 5) L hdom, hth,
      zeta_pow_conj n (hT.shift_sub 1) (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m - n - 1) = F (m - ((n + 1 : ℕ) : ℤ))
    congr 1
    push_cast
    ring

/-- Conjugation by `ζ^{−n}` moves the window `n` levels down. -/
theorem zeta_pow_conj_inv (hψ : ψ 1 = 1) :
    ∀ (n : ℕ) {F : ℤ → Γ} {lo hi : ℤ}, Tame F lo hi → -(3 * s + 3 : ℤ) + n ≤ lo → hi ≤ 3 * s + 3 →
      (zeta Q (6 * s + 5) L ^ n)⁻¹ * lmul Q (6 * s + 5) L (window ψ s F) * zeta Q (6 * s + 5) L ^ n =
        lmul Q (6 * s + 5) L (window ψ s fun m => F (m + n))
  | 0, F, _, _, _, _, _ => by simp
  | n + 1, F, lo, hi, hT, hlo, hhi => by
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    push_cast at hlo
    have hdom : window ψ s (fun m => F (m + 1)) ∈ dom Q (6 * s + 5) :=
      window_mem_dom ψ s (hT.eq_of_le (a := 3 * s + 2 + 1) (b := 3 * s + 3 + 1) (by linarith)
        (by linarith))
    have hth : theta Q (6 * s + 5) (window ψ s fun m => F (m + 1)) = window ψ s F := by
      rw [theta_window ψ s hψ (hT.1 (-(3 * s + 3) - 1 + 1) (by linarith))]
      congr 1
      funext m
      show F (m - 1 + 1) = F m
      rw [sub_add_cancel]
    rw [pow_succ', conj_inv_mul_conj, ← hth, zeta_inv_mul_lmul_theta_mul_zeta Q (6 * s + 5) L hdom,
      zeta_pow_conj_inv n (hT.shift_add 1) (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m + n + 1) = F (m + ((n + 1 : ℕ) : ℤ))
    congr 1
    push_cast
    ring

/-- **`ζ^ℓ (ψ(f(m)))_m ζ^{−ℓ} = (ψ(f(m−ℓ)))_m` for `|ℓ| ≤ r`** (tex l.377–379). -/
theorem zeta_zpow_conj (hψ : ψ 1 = 1) {F : ℤ → Γ} {ℓ : ℤ} (hT : Tame F (-((s + 1 : ℕ) : ℤ)) (s + 1 : ℕ))
    (hℓ : |ℓ| ≤ ((s + 1 : ℕ) : ℤ)) :
    zeta Q (6 * s + 5) L ^ ℓ * lmul Q (6 * s + 5) L (window ψ s F) * (zeta Q (6 * s + 5) L ^ ℓ)⁻¹ =
      lmul Q (6 * s + 5) L (window ψ s fun m => F (m - ℓ)) := by
  have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  have hℓ' := abs_le.mp hℓ
  push_cast at hℓ' hT
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg ℓ
  · rw [zpow_natCast]
    exact zeta_pow_conj ψ s L hψ n hT (by linarith) (by linarith)
  · rw [zpow_neg, zpow_natCast, inv_inv,
      zeta_pow_conj_inv ψ s L hψ n hT (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m + n) = F (m - -(n : ℤ))
    rw [sub_neg_eq_add]

omit [Finite Q] in
theorem lmul_apply' (v : Fin (6 * s + 5 + 2) → Q) (z : (Fin (6 * s + 5 + 2) → Q) × ZMod L) :
    lmul Q (6 * s + 5) L v z = (v * z.1, z.2) :=
  rfl

theorem zeta_inv_snd (z : (Fin (6 * s + 5 + 2) → Q) × ZMod L) :
    ((zeta Q (6 * s + 5) L)⁻¹ z).2 = z.2 - 1 := by
  have h := zeta_apply Q (6 * s + 5) L ((zeta Q (6 * s + 5) L)⁻¹ z)
  rw [Perm.apply_inv_self] at h
  rw [eq_sub_iff_add_eq]
  exact (congrArg Prod.snd h).symm

theorem zeta_zpow_snd (n : ℤ) (z : (Fin (6 * s + 5 + 2) → Q) × ZMod L) :
    ((zeta Q (6 * s + 5) L ^ n) z).2 = z.2 + n := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Perm.mul_apply, ih, zeta_apply]
    push_cast
    ring
  | pred k ih =>
    rw [zpow_sub_one, Perm.mul_apply, ih, zeta_inv_snd]
    push_cast
    ring

end Window

section Models

variable {Γ Q : Type*} [Group Γ] [Group Q] (ψ : Γ → Q) (s L : ℕ) [Finite Q]

/-- **The finite model** `fβ^ℓ ↦ (ψ(f(m)))_{|m| ≤ 3r} ζ^ℓ` (tex l.379). -/
noncomputable def model (g : Perm (Γ × ℤ)) : Perm ((Fin (6 * s + 5 + 2) → Q) × ZMod L) :=
  lmul Q (6 * s + 5) L (window ψ s (levelFunOf g)) * zeta Q (6 * s + 5) L ^ levelShiftOf g

/-- **The model preserves the products** of elements of length at most `r` (tex l.379–380). -/
theorem model_mul (hψ1 : ψ 1 = 1) {E : Set Γ}
    (hψmul : ∀ a ∈ wordBall E (2 * (s + 1)), ∀ b ∈ wordBall E (2 * (s + 1)),
      a * b ∈ wordBall E (2 * (s + 1)) → ψ (a * b) = ψ a * ψ b)
    {g g' : Perm (Γ × ℤ)} {f f' : ℤ → Γ} {ℓ ℓ' : ℤ} (hg : IsLevelForm g f ℓ)
    (hg' : IsLevelForm g' f' ℓ') (hb : LevelBounds E (s + 1) f ℓ) (hb' : LevelBounds E (s + 1) f' ℓ') :
    model ψ s L (g * g') = model ψ s L g * model ψ s L g' := by
  have hgg' := hg.mul hg'
  have hball : ∀ a ∈ wordBall E (s + 1), ∀ b ∈ wordBall E (s + 1), ψ (a * b) = ψ a * ψ b :=
    fun a ha b hb2 => hψmul a (wordBall_mono E (by omega) ha) b (wordBall_mono E (by omega) hb2)
      (by rw [two_mul]; exact mul_mem_wordBall ha hb2)
  simp only [model]
  rw [hgg'.levelShiftOf_eq, hgg'.levelFunOf_eq, hg.levelShiftOf_eq, hg.levelFunOf_eq,
    hg'.levelShiftOf_eq, hg'.levelFunOf_eq, mul_zpow_mul_split,
    zeta_zpow_conj ψ s L hψ1 hb'.tame hb.1, ← map_mul]
  congr 2
  funext k
  exact hball _ (hb.2.1 _) _ (hb'.2.1 _)

/-- **The model is injective on the ball of radius `r`**, as `L > 2r` and `f` is determined by its values for
`|m| ≤ 3r` (tex l.380–382). -/
theorem model_injOn {E : Set Γ} (hψinj : Set.InjOn ψ (wordBall E (2 * (s + 1)))) (hL : 2 * (s + 1) < L)
    {g g' : Perm (Γ × ℤ)} {f f' : ℤ → Γ} {ℓ ℓ' : ℤ} (hg : IsLevelForm g f ℓ)
    (hg' : IsLevelForm g' f' ℓ') (hb : LevelBounds E (s + 1) f ℓ) (hb' : LevelBounds E (s + 1) f' ℓ')
    (h : model ψ s L g = model ψ s L g') : g = g' := by
  have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  simp only [model, hg.levelShiftOf_eq, hg.levelFunOf_eq, hg'.levelShiftOf_eq, hg'.levelFunOf_eq] at h
  have hsnd := congrArg (fun σ : Perm ((Fin (6 * s + 5 + 2) → Q) × ZMod L) => (σ (1, 0)).2) h
  simp only [Perm.mul_apply, lmul_apply', zeta_zpow_snd, zero_add] at hsnd
  have hℓ : ℓ = ℓ' := by
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ℓ ℓ' L).1 hsnd
    have h1 := abs_le.mp hb.1
    have h2 := abs_le.mp hb'.1
    push_cast at h1 h2
    have hL' : (2 * (s + 1) : ℤ) < L := by exact_mod_cast hL
    rcases lt_trichotomy c 0 with hc0 | rfl | hc0
    · nlinarith
    · simp only [mul_zero] at hc
      linarith
    · nlinarith
  subst hℓ
  have hlm : lmul Q (6 * s + 5) L (window ψ s f) = lmul Q (6 * s + 5) L (window ψ s f') :=
    mul_right_cancel h
  have hw : window ψ s f = window ψ s f' := by
    have h3 := congrArg (fun σ : Perm ((Fin (6 * s + 5 + 2) → Q) × ZMod L) => (σ (1, 0)).1) hlm
    simpa [lmul_apply'] using h3
  have hmid : ∀ m : ℤ, -(3 * s + 3 : ℤ) ≤ m → m ≤ 3 * s + 3 → f m = f' m := by
    intro m hm1 hm2
    have hk : (m + (3 * s + 3)).toNat < 6 * s + 5 + 2 := by omega
    have hval := congrFun hw ⟨(m + (3 * s + 3)).toNat, hk⟩
    have hm : (((m + (3 * s + 3)).toNat : ℕ) : ℤ) - (3 * s + 3) = m := by
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    have hval' : ψ (f m) = ψ (f' m) := by
      have e1 : window ψ s f ⟨(m + (3 * s + 3)).toNat, hk⟩ = ψ (f m) := by
        show ψ (f ((((m + (3 * s + 3)).toNat : ℕ) : ℤ) - (3 * s + 3))) = ψ (f m)
        rw [hm]
      have e2 : window ψ s f' ⟨(m + (3 * s + 3)).toNat, hk⟩ = ψ (f' m) := by
        show ψ (f' ((((m + (3 * s + 3)).toNat : ℕ) : ℤ) - (3 * s + 3))) = ψ (f' m)
        rw [hm]
      rw [← e1, ← e2, hval]
    exact hψinj (wordBall_mono E (by omega) (hb.2.1 m)) (wordBall_mono E (by omega) (hb'.2.1 m)) hval'
  have hf : f = f' := by
    funext m
    by_cases h1 : m < -(3 * s + 3 : ℤ)
    · rw [hb.2.2.1 m (by push_cast; linarith), hb'.2.2.1 m (by push_cast; linarith)]
    · by_cases h2 : (3 * s + 3 : ℤ) < m
      · rw [hb.2.2.2 m (by push_cast; linarith), hb'.2.2.2 m (by push_cast; linarith)]
        exact hmid _ (by push_cast; linarith) (by push_cast; linarith)
      · exact hmid m (by linarith) (by linarith)
  subst hf
  exact IsLevelForm.ext hg hg'

end Models

/-- **`Δ` is LEF** (tex l.377–382): on a finite test set, of word length at most `r = s + 1`, the models with
`L = 5r` are injective and preserve the products. -/
theorem isTextbookLEF_levelDelta {Γ : Type*} [Group Γ] (hΓ : IsTextbookLEF Γ) (E : Finset Γ) :
    IsTextbookLEF ↥(levelDelta Γ E) := by
  classical
  intro S
  have hr : ∀ x : ↥(levelDelta Γ E),
      ∃ r, (x : Perm (Γ × ℤ)) ∈ wordBall (insert (levelShift Γ) (levelMul '' (E : Set Γ))) r :=
    fun x => exists_mem_wordBall_of_mem_levelDelta x.2
  choose rad hrad using hr
  have hS : ∀ x ∈ S, (x : Perm (Γ × ℤ)) ∈
      wordBall (insert (levelShift Γ) (levelMul '' (E : Set Γ))) (S.sup rad + 1) :=
    fun x hx => wordBall_mono _ (Nat.le_succ_of_le (Finset.le_sup hx)) (hrad x)
  have hfin : (wordBall (E : Set Γ) (2 * (S.sup rad + 1))).Finite := wordBall_finite E.finite_toSet _
  obtain ⟨H, ψ, hψinj, hψmul⟩ := hΓ hfin.toFinset
  have hψinj' : Set.InjOn ψ (wordBall (E : Set Γ) (2 * (S.sup rad + 1))) := by
    simpa using hψinj
  have hψmul' : ∀ a ∈ wordBall (E : Set Γ) (2 * (S.sup rad + 1)),
      ∀ b ∈ wordBall (E : Set Γ) (2 * (S.sup rad + 1)),
        a * b ∈ wordBall (E : Set Γ) (2 * (S.sup rad + 1)) → ψ (a * b) = ψ a * ψ b :=
    fun a ha b hb hab =>
      hψmul a (hfin.mem_toFinset.2 ha) b (hfin.mem_toFinset.2 hb) (hfin.mem_toFinset.2 hab)
  have hone : (1 : Γ) ∈ wordBall (E : Set Γ) (2 * (S.sup rad + 1)) := one_mem_wordBall _ _
  have hψ1 : ψ 1 = 1 := by
    have h := hψmul' 1 hone 1 hone (by rw [one_mul]; exact hone)
    rw [one_mul] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  haveI : NeZero (5 * (S.sup rad + 1)) := ⟨by omega⟩
  refine ⟨⟨Perm ((Fin (6 * S.sup rad + 5 + 2) → H) × ZMod (5 * (S.sup rad + 1))), inferInstance,
    inferInstance, inferInstance⟩, fun x => model ψ (S.sup rad) (5 * (S.sup rad + 1)) (x : Perm (Γ × ℤ)),
    ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨f, ℓ, hf, hb⟩ := exists_levelForm_of_mem_wordBall (hS x hx)
    obtain ⟨f', ℓ', hf', hb'⟩ := exists_levelForm_of_mem_wordBall (hS y hy)
    exact Subtype.ext (model_injOn ψ (S.sup rad) (5 * (S.sup rad + 1)) hψinj' (by omega) hf hf' hb hb' hxy)
  · intro x hx y hy _
    obtain ⟨f, ℓ, hf, hb⟩ := exists_levelForm_of_mem_wordBall (hS x hx)
    obtain ⟨f', ℓ', hf', hb'⟩ := exists_levelForm_of_mem_wordBall (hS y hy)
    exact model_mul ψ (S.sup rad) (5 * (S.sup rad + 1)) hψ1 hψmul' hf hf' hb hb'

end LevelShiftDelta
end GroupApproximation
