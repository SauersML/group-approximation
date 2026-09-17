import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.PrintedKappa
import GroupApproximation.GroupTheory.LevelShiftDeltaModels
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline`: the finite models `fβ^ℓ ↦ (ψ(f(m)))_{|m| ≤ 3λ} ζ^ℓ` for the printed `ζ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline`:

* tex l.639–642, sentence b4d347ea01a7:
  > As f is trivial below −λ and constant from λ on, ζ^ℓ (ψ(f(m)))_m ζ^{−ℓ} = (ψ(f(m−ℓ)))_m for |ℓ| ≤ λ.
* tex l.642–645, sentence 20cd8bd5a5e9:
  > So fβ^ℓ ↦ (ψ(f(m)))_{|m|≤3λ} ζ^ℓ preserves the products that stay in the ball of radius λ, and it is injective
  > there, as 5λ > 2λ and f is determined by its values for |m| ≤ 3λ.

## Conventions

As in `HalflineA/PrintedKappa`: `λ = s + 1`, the window `Q^{[−3λ,3λ]}` is `Fin (6s + 5 + 2) → Q` with position `k`
standing for the level `k − 3λ` (`LevelShiftDelta.window`), and `ζ` is `printedZeta`, built from the printed `κ`.

## Proof route

The arguments of `LevelShiftDeltaModels` (`zeta_pow_conj`, ..., `model_injOn`), run for the printed `ζ` with the law
`printedZeta_mul_lmul_mul_printedZeta_inv` (`ζ v ζ⁻¹ = θ(v)` on the domain of `θ`):

* `printedZeta_pow_conj`, `printedZeta_pow_conj_inv`: induction on `n`. If `F` is trivial below `lo ≥ −3λ` and
  constant from `hi` with `hi + n ≤ 3λ`, the window of `F` lies in the domain of `θ` (`window_mem_dom`) and
  `θ` shifts it one level up (`theta_window`).
* `printedZeta_zpow_conj`: the sign cases of `ℓ`, with `lo = −λ`, `hi = λ` and `|ℓ| ≤ λ`, so `λ + λ ≤ 3λ`.
* `printedZeta_zpow_snd`: `ζ^n` adds `n` in `ℤ/L`.
* `printedModel_mul`: `fβ^ℓ f'β^{ℓ'} = (f · f'(· − ℓ)) β^{ℓ+ℓ'}`, and the conjugation law moves `ζ^ℓ` across the
  window of `f'`. `ψ` is multiplicative on pairs of the ball of radius `λ` (their products lie in the ball of radius
  `2λ`).
* `printedModel_injOn`: the `ℤ/L` coordinate of `(1, 0)` gives `ℓ ≡ ℓ'` mod `L = 5λ > 2λ`, so `ℓ = ℓ'`. Then the
  windows agree, so `f = f'` on `|m| ≤ 3λ` by injectivity of `ψ` on the ball of radius `2λ`, and everywhere since both
  are trivial below `−λ` and constant from `λ`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HalflineA

open Equiv ShiftTransversalBijection LevelShiftDelta

section Conjugation

variable {Γ Q : Type*} [Group Γ] [Group Q] (ψ : Γ → Q) (s L : ℕ)

/-- Conjugation by `ζ^n` moves the window `n` levels up. -/
theorem printedZeta_pow_conj (hψ : ψ 1 = 1) :
    ∀ (n : ℕ) {F : ℤ → Γ} {lo hi : ℤ}, Tame F lo hi → -(3 * s + 3 : ℤ) ≤ lo → hi + n ≤ 3 * s + 3 →
      printedZeta Q (6 * s + 5) L ^ n * lmul Q (6 * s + 5) L (window ψ s F) *
          (printedZeta Q (6 * s + 5) L ^ n)⁻¹ =
        lmul Q (6 * s + 5) L (window ψ s fun m => F (m - n))
  | 0, F, _, _, _, _, _ => by simp
  | n + 1, F, lo, hi, hT, hlo, hhi => by
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    push_cast at hhi
    have hdom : window ψ s F ∈ dom Q (6 * s + 5) :=
      window_mem_dom ψ s (hT.eq_of_le (by linarith) (by linarith))
    have hth : theta Q (6 * s + 5) (window ψ s F) = window ψ s fun m => F (m - 1) :=
      theta_window ψ s hψ (hT.1 (-(3 * s + 3) - 1) (by linarith))
    rw [pow_succ, conj_mul_conj, printedZeta_mul_lmul_mul_printedZeta_inv Q (6 * s + 5) L hdom, hth,
      printedZeta_pow_conj hψ n (hT.shift_sub 1) (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m - n - 1) = F (m - ((n + 1 : ℕ) : ℤ))
    congr 1
    push_cast
    ring

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedZeta_pow_conj

/-- Conjugation by `ζ^{−n}` moves the window `n` levels down. -/
theorem printedZeta_pow_conj_inv (hψ : ψ 1 = 1) :
    ∀ (n : ℕ) {F : ℤ → Γ} {lo hi : ℤ}, Tame F lo hi → -(3 * s + 3 : ℤ) + n ≤ lo → hi ≤ 3 * s + 3 →
      (printedZeta Q (6 * s + 5) L ^ n)⁻¹ * lmul Q (6 * s + 5) L (window ψ s F) *
          printedZeta Q (6 * s + 5) L ^ n =
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
    rw [pow_succ', conj_inv_mul_conj, ← hth,
      printedZeta_inv_mul_lmul_theta_mul_printedZeta Q (6 * s + 5) L hdom,
      printedZeta_pow_conj_inv hψ n (hT.shift_add 1) (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m + n + 1) = F (m + ((n + 1 : ℕ) : ℤ))
    congr 1
    push_cast
    ring

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedZeta_pow_conj_inv

/-- **`ζ^ℓ (ψ(f(m)))_m ζ^{−ℓ} = (ψ(f(m−ℓ)))_m` for `|ℓ| ≤ λ`**, for `F` trivial below `−λ` and constant from `λ`. -/
theorem printedZeta_zpow_conj (hψ : ψ 1 = 1) {F : ℤ → Γ} {ℓ : ℤ}
    (hT : Tame F (-((s + 1 : ℕ) : ℤ)) (s + 1 : ℕ)) (hℓ : |ℓ| ≤ ((s + 1 : ℕ) : ℤ)) :
    printedZeta Q (6 * s + 5) L ^ ℓ * lmul Q (6 * s + 5) L (window ψ s F) *
        (printedZeta Q (6 * s + 5) L ^ ℓ)⁻¹ =
      lmul Q (6 * s + 5) L (window ψ s fun m => F (m - ℓ)) := by
  have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  have hℓ' := abs_le.mp hℓ
  push_cast at hℓ' hT
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg ℓ
  · rw [zpow_natCast]
    exact printedZeta_pow_conj ψ s L hψ n hT (by linarith) (by linarith)
  · rw [zpow_neg, zpow_natCast, inv_inv,
      printedZeta_pow_conj_inv ψ s L hψ n hT (by linarith) (by linarith)]
    congr 2
    funext m
    show F (m + n) = F (m - -(n : ℤ))
    rw [sub_neg_eq_add]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedZeta_zpow_conj

theorem printedZeta_inv_snd (z : (Fin (6 * s + 5 + 2) → Q) × ZMod L) :
    ((printedZeta Q (6 * s + 5) L)⁻¹ z).2 = z.2 - 1 := by
  have h := printedZeta_apply Q (6 * s + 5) L ((printedZeta Q (6 * s + 5) L)⁻¹ z)
  have hz : printedZeta Q (6 * s + 5) L ((printedZeta Q (6 * s + 5) L)⁻¹ z) = z := by
    simp
  rw [hz] at h
  rw [eq_sub_iff_add_eq]
  exact (congrArg Prod.snd h).symm

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedZeta_inv_snd

/-- `ζ^n` adds `n` in the coordinate `ℤ/L`. -/
theorem printedZeta_zpow_snd (n : ℤ) (z : (Fin (6 * s + 5 + 2) → Q) × ZMod L) :
    ((printedZeta Q (6 * s + 5) L ^ n) z).2 = z.2 + n := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Perm.mul_apply, ih, printedZeta_apply]
    push_cast
    ring
  | pred k ih =>
    rw [zpow_sub_one, Perm.mul_apply, ih, printedZeta_inv_snd]
    push_cast
    ring

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedZeta_zpow_snd

end Conjugation

section Models

variable {Γ Q : Type*} [Group Γ] [Group Q] (ψ : Γ → Q) (s L : ℕ)

/-- **The finite model** `fβ^ℓ ↦ (ψ(f(m)))_{|m| ≤ 3λ} ζ^ℓ` (tex l.642–643), for the printed `ζ`. -/
noncomputable def printedModel (g : Perm (Γ × ℤ)) : Perm ((Fin (6 * s + 5 + 2) → Q) × ZMod L) :=
  lmul Q (6 * s + 5) L (window ψ s (levelFunOf g)) * printedZeta Q (6 * s + 5) L ^ levelShiftOf g

/-- The model preserves the products of elements of length at most `λ`. -/
theorem printedModel_mul (hψ1 : ψ 1 = 1) {E : Set Γ}
    (hψmul : ∀ a ∈ wordBall E (2 * (s + 1)), ∀ b ∈ wordBall E (2 * (s + 1)),
      a * b ∈ wordBall E (2 * (s + 1)) → ψ (a * b) = ψ a * ψ b)
    {g g' : Perm (Γ × ℤ)} {f f' : ℤ → Γ} {ℓ ℓ' : ℤ} (hg : IsLevelForm g f ℓ)
    (hg' : IsLevelForm g' f' ℓ') (hb : LevelBounds E (s + 1) f ℓ) (hb' : LevelBounds E (s + 1) f' ℓ') :
    printedModel ψ s L (g * g') = printedModel ψ s L g * printedModel ψ s L g' := by
  have hgg' := hg.mul hg'
  have hball : ∀ a ∈ wordBall E (s + 1), ∀ b ∈ wordBall E (s + 1), ψ (a * b) = ψ a * ψ b :=
    fun a ha b hb2 => hψmul a (wordBall_mono E (by omega) ha) b (wordBall_mono E (by omega) hb2)
      (by rw [two_mul]; exact mul_mem_wordBall ha hb2)
  simp only [printedModel]
  rw [hgg'.levelShiftOf_eq, hgg'.levelFunOf_eq, hg.levelShiftOf_eq, hg.levelFunOf_eq,
    hg'.levelShiftOf_eq, hg'.levelFunOf_eq, mul_zpow_mul_split,
    printedZeta_zpow_conj ψ s L hψ1 hb'.tame hb.1, ← map_mul]
  congr 2
  funext k
  exact hball _ (hb.2.1 _) _ (hb'.2.1 _)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedModel_mul

/-- The model is injective on the ball of radius `λ`, as `L > 2λ` and `f` is determined by its values for
`|m| ≤ 3λ`. -/
theorem printedModel_injOn {E : Set Γ} (hψinj : Set.InjOn ψ (wordBall E (2 * (s + 1)))) (hL : 2 * (s + 1) < L)
    {g g' : Perm (Γ × ℤ)} {f f' : ℤ → Γ} {ℓ ℓ' : ℤ} (hg : IsLevelForm g f ℓ)
    (hg' : IsLevelForm g' f' ℓ') (hb : LevelBounds E (s + 1) f ℓ) (hb' : LevelBounds E (s + 1) f' ℓ')
    (h : printedModel ψ s L g = printedModel ψ s L g') : g = g' := by
  have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  simp only [printedModel, hg.levelShiftOf_eq, hg.levelFunOf_eq, hg'.levelShiftOf_eq, hg'.levelFunOf_eq] at h
  have hsnd := congrArg (fun σ : Perm ((Fin (6 * s + 5 + 2) → Q) × ZMod L) => (σ (1, 0)).2) h
  simp only [Perm.mul_apply, lmul_apply', printedZeta_zpow_snd, zero_add] at hsnd
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

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.printedModel_injOn

end Models

/-- A map preserving the products that stay in a ball maps `1` to `1`. -/
theorem map_one_of_mul_wordBall {Γ Q : Type*} [Group Γ] [Group Q] {ψ : Γ → Q} {E : Set Γ} {r : ℕ}
    (hψmul : ∀ a ∈ wordBall E r, ∀ b ∈ wordBall E r, a * b ∈ wordBall E r → ψ (a * b) = ψ a * ψ b) :
    ψ 1 = 1 := by
  have hone : (1 : Γ) ∈ wordBall E r := one_mem_wordBall E r
  have h := hψmul 1 hone 1 hone (by rw [one_mul]; exact hone)
  rw [one_mul] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.map_one_of_mul_wordBall

/-- **`ζ^ℓ (ψ(f(m)))_m ζ^{−ℓ} = (ψ(f(m−ℓ)))_m` for `|ℓ| ≤ λ`** (tex l.639–642), at `λ = s + 1` and `L = 5λ`. Here
`ψ` preserves the products that stay in the ball of radius `2λ` (so `ψ(1) = 1`), `f` is trivial below `−λ` and constant
from `λ` on, and `(ψ(f(m)))_m` is the window `k ↦ ψ(f(k − 3λ))` of `Q^{[−3λ,3λ]}`. -/
theorem manuscriptSentence_halflineZetaConjugation {Γ Q : Type*} [Group Γ] [Group Q] (E : Set Γ) (s : ℕ)
    (ψ : Γ → Q)
    (hψmul : ∀ a ∈ wordBall E (2 * (s + 1)), ∀ b ∈ wordBall E (2 * (s + 1)),
      a * b ∈ wordBall E (2 * (s + 1)) → ψ (a * b) = ψ a * ψ b)
    (f : ℤ → Γ) (hlow : ∀ m, m < -((s + 1 : ℕ) : ℤ) → f m = 1)
    (hhigh : ∀ m, ((s + 1 : ℕ) : ℤ) < m → f m = f ((s + 1 : ℕ) : ℤ)) (ℓ : ℤ) (hℓ : |ℓ| ≤ ((s + 1 : ℕ) : ℤ)) :
    printedZeta Q (6 * s + 5) (5 * (s + 1)) ^ ℓ *
        lmul Q (6 * s + 5) (5 * (s + 1)) (fun k : Fin (6 * s + 5 + 2) => ψ (f ((k : ℕ) - (3 * s + 3 : ℤ)))) *
        (printedZeta Q (6 * s + 5) (5 * (s + 1)) ^ ℓ)⁻¹ =
      lmul Q (6 * s + 5) (5 * (s + 1)) (fun k : Fin (6 * s + 5 + 2) => ψ (f ((k : ℕ) - (3 * s + 3 : ℤ) - ℓ))) :=
  printedZeta_zpow_conj ψ s (5 * (s + 1)) (map_one_of_mul_wordBall hψmul)
    (show Tame f (-((s + 1 : ℕ) : ℤ)) ((s + 1 : ℕ) : ℤ) from ⟨hlow, hhigh⟩) hℓ

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflineZetaConjugation

/-- **The finite models** (tex l.642–645), at `λ = s + 1` and `L = 5λ`. Let `ψ` be injective on the ball of radius
`2λ` of `Γ` in `E` and preserve the products that stay in it. The map `printedModel` sends `fβ^ℓ` to
`(ψ(f(m)))_{|m| ≤ 3λ} ζ^ℓ`. It preserves the products that stay in the ball of radius `λ` of
`Δ = ⟨β, h_γ : γ ∈ E⟩`, and it is injective there. -/
theorem manuscriptSentence_halflinePrintedModel {Γ Q : Type*} [Group Γ] [Group Q] (E : Set Γ) (s : ℕ)
    (ψ : Γ → Q) (hψinj : Set.InjOn ψ (wordBall E (2 * (s + 1))))
    (hψmul : ∀ a ∈ wordBall E (2 * (s + 1)), ∀ b ∈ wordBall E (2 * (s + 1)),
      a * b ∈ wordBall E (2 * (s + 1)) → ψ (a * b) = ψ a * ψ b) :
    (∀ (g : Perm (Γ × ℤ)) (f : ℤ → Γ) (ℓ : ℤ), IsLevelForm g f ℓ →
      printedModel ψ s (5 * (s + 1)) g =
        lmul Q (6 * s + 5) (5 * (s + 1)) (fun k : Fin (6 * s + 5 + 2) => ψ (f ((k : ℕ) - (3 * s + 3 : ℤ)))) *
          printedZeta Q (6 * s + 5) (5 * (s + 1)) ^ ℓ) ∧
    (∀ g ∈ wordBall (insert (levelShift Γ) (levelMul '' E)) (s + 1),
      ∀ g' ∈ wordBall (insert (levelShift Γ) (levelMul '' E)) (s + 1),
        g * g' ∈ wordBall (insert (levelShift Γ) (levelMul '' E)) (s + 1) →
          printedModel ψ s (5 * (s + 1)) (g * g') =
            printedModel ψ s (5 * (s + 1)) g * printedModel ψ s (5 * (s + 1)) g') ∧
    Set.InjOn (printedModel ψ s (5 * (s + 1))) (wordBall (insert (levelShift Γ) (levelMul '' E)) (s + 1)) := by
  refine ⟨fun g f ℓ hg => ?_, fun g hg g' hg' _ => ?_, ?_⟩
  · have h1 : levelShiftOf g = ℓ := hg.levelShiftOf_eq
    have h2 : levelFunOf g = f := hg.levelFunOf_eq
    subst h1
    subst h2
    rfl
  · obtain ⟨f, ℓ, hf, hb⟩ := exists_levelForm_of_mem_wordBall hg
    obtain ⟨f', ℓ', hf', hb'⟩ := exists_levelForm_of_mem_wordBall hg'
    exact printedModel_mul ψ s (5 * (s + 1)) (map_one_of_mul_wordBall hψmul) hψmul hf hf' hb hb'
  · intro g hg g' hg' h
    obtain ⟨f, ℓ, hf, hb⟩ := exists_levelForm_of_mem_wordBall hg
    obtain ⟨f', ℓ', hf', hb'⟩ := exists_levelForm_of_mem_wordBall hg'
    exact printedModel_injOn ψ s (5 * (s + 1)) hψinj (by omega) hf hf' hb hb' h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflinePrintedModel

end HalflineA
end SimpleKazhdanSofic
end GroupApproximation
