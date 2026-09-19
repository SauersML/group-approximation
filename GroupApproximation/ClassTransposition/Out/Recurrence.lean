import GroupApproximation.ClassTransposition.Out.Dilation
import GroupApproximation.ClassTransposition.Out.ModP
import GroupApproximation.ClassTransposition.Out.LocalGlobal

/-!
# Kourovka 17.57, step 3: a continuous normalizer is linearly recurrent over `ℚ`

Let `h` conjugate `CT(ℤ)` into itself and be profinitely continuous. Then `Φ(n) = h(n)`
(`n ∈ ℕ`) satisfies a nonzero rational linear recurrence
(`exists_rat_recurrence_of_normalizer`).

- The base-2 recursions `Φ(2k + e) = β_e(k) Φ(k) + α_e(k)` come from step 1
  (`Out/Dilation.lean`). Their coefficients are periodic, and `β_e ≠ 0` because `h` is
  injective.
- For every large prime `p`, reduce them mod `p`. Continuity makes `Φ mod p` periodic. Then
  `exists_short_recurrence` (`Out/ModP.lean`) gives a nonzero mod-`p` recurrence of order
  `≤ 2ᶜ · 2P`, uniformly in `p`.
- The local–global Lemma `lem: rational` (`Out/LocalGlobal.lean`) lifts these to `ℚ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- Reduction of a rational number modulo `p`. -/
def ratMod (p : ℕ) (q : ℚ) : ZMod p := (q.num : ZMod p) * ((q.den : ℕ) : ZMod p)⁻¹

theorem ratMod_affine {p : ℕ} [Fact p.Prime] {x y : ℤ} {q₁ q₂ : ℚ}
    (h1 : ¬ p ∣ q₁.den) (h2 : ¬ p ∣ q₂.den) (h : (x : ℚ) = q₁ * y + q₂) :
    (x : ZMod p) = ratMod p q₁ * y + ratMod p q₂ := by
  have hz : (q₁.den : ℤ) * q₂.den * x = q₁.num * q₂.den * y + q₂.num * q₁.den := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h, ← Rat.mul_den_eq_num q₁, ← Rat.mul_den_eq_num q₂]
    ring
  have hd1 : ((q₁.den : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h1
  have hd2 : ((q₂.den : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h2
  have e1 : ((q₁.den : ℕ) : ZMod p) * ((q₁.den : ℕ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hd1
  have e2 : ((q₂.den : ℕ) : ZMod p) * ((q₂.den : ℕ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hd2
  have hzp := congrArg (Int.cast : ℤ → ZMod p) hz
  push_cast at hzp
  unfold ratMod
  linear_combination (((q₁.den : ℕ) : ZMod p)⁻¹ * ((q₂.den : ℕ) : ZMod p)⁻¹) * hzp
    - ((x : ZMod p) * ((q₂.den : ℕ) : ZMod p) * ((q₂.den : ℕ) : ZMod p)⁻¹) * e1
    - (x : ZMod p) * e2
    + ((q₁.num : ZMod p) * ((q₁.den : ℕ) : ZMod p)⁻¹ * (y : ZMod p)) * e2
    + ((q₂.num : ZMod p) * ((q₂.den : ℕ) : ZMod p)⁻¹) * e1

theorem ratMod_ne_zero {p : ℕ} [Fact p.Prime] {q : ℚ} (h1 : ¬ (p : ℤ) ∣ q.num)
    (h2 : ¬ p ∣ q.den) : ratMod p q ≠ 0 := by
  unfold ratMod
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h1
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h2

/-- The dilation coefficient `β` never vanishes, because `h` is injective. -/
theorem dilation_coeff_ne_zero {h : Equiv.Perm ℤ} {b e P : ℤ} (hP : 0 < P) (hb : b ≠ 0)
    {β α : ℤ → ℚ} (hβ : ∀ k, β (k + P) = β k) (hα : ∀ k, α (k + P) = α k)
    (hrec : ∀ k, (h (b * k + e) : ℚ) = β k * h k + α k) (k : ℤ) : β k ≠ 0 := by
  intro h0
  have h1 := hrec k
  have h2 := hrec (k + P)
  rw [hβ, hα, h0, zero_mul, zero_add] at h2
  rw [h0, zero_mul, zero_add] at h1
  have h3 : h (b * (k + P) + e) = h (b * k + e) := by exact_mod_cast h2.trans h1.symm
  have h4 := h.injective h3
  have h5 : b * P = 0 := by linarith
  rcases mul_eq_zero.mp h5 with h6 | h6 <;> omega

theorem periodic_int_mul {γ : ℤ → ℚ} {Q : ℤ} (hγ : ∀ k, γ (k + Q) = γ k) :
    ∀ (q : ℕ) (k : ℤ), γ (k + Q * q) = γ k := by
  intro q
  induction q with
  | zero => intro k; simp
  | succ q ih =>
    intro k
    rw [show k + Q * ((q + 1 : ℕ) : ℤ) = k + Q * q + Q by push_cast; ring, hγ, ih]

/-- **Step 3.** A profinitely continuous permutation of `ℤ` conjugating `CT(ℤ)` into itself
satisfies, on `ℕ`, a nonzero linear recurrence over `ℚ`. -/
theorem exists_rat_recurrence_of_normalizer {h : Equiv.Perm ℤ}
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (hrcwa : ∀ g ∈ classTranspositionGroup, IsResidueClassWiseAffine g)
    (hc : IsProfinitelyContinuous h) :
    ∃ D : ℕ, ∃ c : Fin D → ℚ, c ≠ 0 ∧
      ∀ m : ℕ, ∑ j : Fin D, c j * (h ((m + j : ℕ) : ℤ) : ℚ) = 0 := by
  classical
  obtain ⟨P₀, hP₀, β₀, α₀, hβ₀, hα₀, hr₀⟩ :=
    dilation_recursion h₁ hrcwa hc (b := 2) (e := 0) le_rfl le_rfl (by norm_num)
  obtain ⟨P₁, hP₁, β₁, α₁, hβ₁, hα₁, hr₁⟩ :=
    dilation_recursion h₁ hrcwa hc (b := 2) (e := 1) le_rfl (by norm_num) (by norm_num)
  have hβ₀0 := dilation_coeff_ne_zero hP₀ two_ne_zero hβ₀ hα₀ hr₀
  have hβ₁0 := dilation_coeff_ne_zero hP₁ two_ne_zero hβ₁ hα₁ hr₁
  -- a common period `P`, as a natural number
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, (P : ℤ) = P₀ * P₁ :=
    ⟨(P₀ * P₁).toNat, Int.toNat_of_nonneg (mul_pos hP₀ hP₁).le⟩
  have hP : 0 < P := by
    have := mul_pos hP₀ hP₁
    rw [← hPdef] at this
    exact_mod_cast this
  have hcommon : ∀ {γ : ℤ → ℚ} {Q : ℤ}, (∀ k, γ (k + Q) = γ k) → 0 < Q → Q ∣ P₀ * P₁ →
      ∀ k : ℕ, γ ((k + P : ℕ) : ℤ) = γ k := by
    intro γ Q hγ hQ hQP k
    obtain ⟨q, hq⟩ := hQP
    have hq0 : 0 ≤ q := by
      have hpos := mul_pos hP₀ hP₁
      rw [hq] at hpos
      by_contra hneg
      push Not at hneg
      nlinarith
    have := periodic_int_mul hγ q.toNat k
    rw [Int.toNat_of_nonneg hq0, ← hq, ← hPdef] at this
    push_cast
    exact this
  let B : ℕ → ℕ → ℚ := fun e k => if e = 0 then β₀ k else β₁ k
  let A : ℕ → ℕ → ℚ := fun e k => if e = 0 then α₀ k else α₁ k
  have hB : ∀ e k, B e (k + P) = B e k := by
    intro e k
    by_cases he : e = 0
    · simp only [B, if_pos he]
      exact hcommon hβ₀ hP₀ ⟨P₁, rfl⟩ k
    · simp only [B, if_neg he]
      exact hcommon hβ₁ hP₁ ⟨P₀, by ring⟩ k
  have hA : ∀ e k, A e (k + P) = A e k := by
    intro e k
    by_cases he : e = 0
    · simp only [A, if_pos he]
      exact hcommon hα₀ hP₀ ⟨P₁, rfl⟩ k
    · simp only [A, if_neg he]
      exact hcommon hα₁ hP₁ ⟨P₀, by ring⟩ k
  have hB0 : ∀ e k, B e k ≠ 0 := by
    intro e k
    by_cases he : e = 0
    · simp only [B, if_pos he]; exact hβ₀0 k
    · simp only [B, if_neg he]; exact hβ₁0 k
  have hrecQ : ∀ e k, e < 2 →
      (h ((2 * k + e : ℕ) : ℤ) : ℚ) = B e k * h (k : ℤ) + A e k := by
    intro e k he
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · show (h ((2 * k + 0 : ℕ) : ℤ) : ℚ) = β₀ k * h (k : ℤ) + α₀ k
      have := hr₀ k
      rw [show ((2 * k + 0 : ℕ) : ℤ) = 2 * (k : ℤ) + 0 by push_cast; ring]
      exact this
    · show (h ((2 * k + 1 : ℕ) : ℤ) : ℚ) = β₁ k * h (k : ℤ) + α₁ k
      have := hr₁ k
      rw [show ((2 * k + 1 : ℕ) : ℤ) = 2 * (k : ℤ) + 1 by push_cast; ring]
      exact this
  -- the finitely many bad primes
  obtain ⟨c, P', hP', hPc⟩ := Nat.exists_eq_two_pow_mul_odd hP.ne'
  let bad : ℕ → ℕ := fun k => (B 0 k).num.natAbs + (B 0 k).den + (A 0 k).den +
    (B 1 k).num.natAbs + (B 1 k).den + (A 1 k).den
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℕ, Bd = (Finset.range P).sup bad := ⟨_, rfl⟩
  have hbad : ∀ e k, e < 2 → (B e k).num.natAbs ≤ Bd ∧ (B e k).den ≤ Bd ∧ (A e k).den ≤ Bd := by
    intro e k he
    have hk : bad (k % P) ≤ Bd := by
      rw [hBd]
      exact Finset.le_sup (Finset.mem_range.mpr (Nat.mod_lt k hP))
    have eB := periodic_mod (hB e) k
    have eA := periodic_mod (hA e) k
    rw [← eB, ← eA]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;> simp only [bad] at hk <;> omega
  refine ⟨2 ^ c * (2 * P) + 1, exists_rat_recurrence_of_mod_primes (f := fun n => h n)
    (fun N => ?_)⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + Bd + 1)
  haveI := Fact.mk hp
  have hden : ∀ q : ℚ, q.den ≤ Bd → ¬ p ∣ q.den := fun q hq hdvd =>
    absurd (Nat.le_of_dvd q.pos hdvd) (by omega)
  have hnum : ∀ q : ℚ, q ≠ 0 → q.num.natAbs ≤ Bd → ¬ (p : ℤ) ∣ q.num := by
    intro q hq hle hdvd
    have h1 := Int.natCast_dvd.mp hdvd
    have h2 : 0 < q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq)
    have := Nat.le_of_dvd h2 h1
    omega
  obtain ⟨T, hT, hTdiv⟩ := hc p (by exact_mod_cast hp.pos)
  have hper : ∀ n : ℕ, ((h ((n + T.toNat : ℕ) : ℤ) : ℤ) : ZMod p) = ((h (n : ℤ) : ℤ) : ZMod p) := by
    intro n
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply hTdiv
    refine ⟨-1, ?_⟩
    push_cast
    rw [Int.toNat_of_nonneg hT.le]
    ring
  obtain ⟨g, hg0, hg⟩ := exists_short_recurrence (F := ZMod p)
    (f := fun n => ((h (n : ℤ) : ℤ) : ZMod p))
    (β := fun e k => ratMod p (B e k)) (α := fun e k => ratMod p (A e k)) hP hPc hP'
    (fun e k => congrArg (ratMod p) (hB e k)) (fun e k => congrArg (ratMod p) (hA e k))
    (fun k => ratMod_ne_zero (hnum _ (hB0 0 k) (hbad 0 k (by norm_num)).1)
      (hden _ (hbad 0 k (by norm_num)).2.1))
    (fun e k he => ratMod_affine (hden _ (hbad e k he).2.1) (hden _ (hbad e k he).2.2)
      (hrecQ e k he))
    (by have := Int.toNat_of_nonneg hT.le; omega) hper
  exact ⟨p, hp, by omega, g, hg0, fun m => hg m⟩

end GroupApproximation.ClassTransposition.Out
