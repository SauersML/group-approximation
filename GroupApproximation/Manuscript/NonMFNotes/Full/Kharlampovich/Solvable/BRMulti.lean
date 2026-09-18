/-
Copyright (c) 2026. All rights reserved.
-/
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.BRFamily
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.BRPw
import Mathlib.Tactic.Group

/-!
# The multi-variable Baumslag--Remeslennikov lemma (KMS, Lemma lBRG)

Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4, Lemma `lBRG` (`p = 2`), in the
form needed for the letters `x_{j,S}` of the Kharlampovich group.

Let `a n, a' n` (`n : Fin K`) be pairwise commuting letters and `x : ι → G` a family such
that each `x i` is, for each coordinate `n`, either *active* (`a'_n x a'_n⁻¹ = a_n x a_n⁻¹ x⁻¹`)
or *inert* (commutes with `a_n` and `a'_n`). If `x i` commutes with every `x j` conjugated by a
product `∏ a_n^{β_n}` with `β_n ∈ {-1, 0, 1}`, then all conjugates of the `x i` by products
`∏ a_n^{β_n} a_n'^{γ_n}` pairwise commute (`BR.multi_commute`).

Proof: induction on the number of coordinates whose exponents are unconstrained; each step
is the one-variable lemma `BR.conj_commute`, applied to a two-element family.
-/

namespace GroupApproximation.Full.Kharlampovich
namespace KMS
namespace BR

variable {G : Type*} [Group G] {K : ℕ}

/-! ### One coordinate -/

theorem conj_fix {Q b : G} (h : Commute Q b) : Q⁻¹ * b * Q = b := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

theorem conj_triv {u a a' : G} (h : Commute u a ∧ Commute u a') (p q : ℤ) :
    (a ^ p * a' ^ q)⁻¹ * u * (a ^ p * a' ^ q) = u :=
  conj_fix ((h.1.zpow_right p).mul_right (h.2.zpow_right q)).symm

theorem conj_mul_eq (y P c : G) : (P * c)⁻¹ * y * (P * c) = c⁻¹ * (P⁻¹ * y * P) * c := by
  simp only [mul_inv_rev, mul_assoc]

/-- Activity or inertness of `y` survives conjugation by an element commuting with `a, a'`. -/
theorem act_conj {y a a' Q : G} (hQa : Commute Q a) (hQa' : Commute Q a')
    (h : a' * y * a'⁻¹ = a * y * a⁻¹ * y⁻¹ ∨ (Commute y a ∧ Commute y a')) :
    a' * (Q⁻¹ * y * Q) * a'⁻¹ = a * (Q⁻¹ * y * Q) * a⁻¹ * (Q⁻¹ * y * Q)⁻¹ ∨
      (Commute (Q⁻¹ * y * Q) a ∧ Commute (Q⁻¹ * y * Q) a') := by
  have e : ∀ b : G, Commute Q b → ∀ z : G,
      b * (Q⁻¹ * z * Q) * b⁻¹ = Q⁻¹ * (b * z * b⁻¹) * Q := by
    intro b hb z
    have h1 : b * Q⁻¹ = Q⁻¹ * b := hb.inv_left.eq.symm
    have h2 : Q * b⁻¹ = b⁻¹ * Q := hb.inv_right.eq
    calc b * (Q⁻¹ * z * Q) * b⁻¹ = b * Q⁻¹ * z * (Q * b⁻¹) := by simp only [mul_assoc]
      _ = Q⁻¹ * b * z * (b⁻¹ * Q) := by rw [h1, h2]
      _ = Q⁻¹ * (b * z * b⁻¹) * Q := by simp only [mul_assoc]
  rcases h with h | h
  · left
    rw [e a' hQa' y, h, e a hQa y]
    group
  · right
    have h1 := commute_conj h.1 Q
    have h2 := commute_conj h.2 Q
    rw [conj_fix hQa] at h1
    rw [conj_fix hQa'] at h2
    exact ⟨h1, h2⟩

/-- The one-variable lemma for two elements, each active or inert. -/
theorem pair_commute {u v a a' : G} (haa' : Commute a a') (huv : Commute u v)
    (huu : Commute u (a⁻¹ * u * a)) (hu1 : Commute u (a⁻¹ * v * a))
    (hv1 : Commute v (a⁻¹ * u * a)) (hvv : Commute v (a⁻¹ * v * a))
    (hu : a' * u * a'⁻¹ = a * u * a⁻¹ * u⁻¹ ∨ (Commute u a ∧ Commute u a'))
    (hv : a' * v * a'⁻¹ = a * v * a⁻¹ * v⁻¹ ∨ (Commute v a ∧ Commute v a'))
    (p q p' q' : ℤ) :
    Commute ((a ^ p * a' ^ q)⁻¹ * u * (a ^ p * a' ^ q))
      ((a ^ p' * a' ^ q')⁻¹ * v * (a ^ p' * a' ^ q')) := by
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · have hC0 : ∀ b b' : Bool, Commute (cond b u v) (cond b' u v) := by
        rintro (_ | _) (_ | _)
        exacts [Commute.refl v, huv.symm, huv, Commute.refl u]
      have hC : ∀ b b' : Bool, Commute (cond b u v) (a⁻¹ * cond b' u v * a) := by
        rintro (_ | _) (_ | _)
        exacts [hvv, hv1, hu1, huu]
      have hE : ∀ b : Bool,
          a' * cond b u v * a'⁻¹ = a * cond b u v * a⁻¹ * (cond b u v)⁻¹ := by
        rintro (_ | _)
        exacts [hv, hu]
      exact conj_commute (fun b : Bool => cond b u v) a a' hC0 hC haa' hE true false
        p q p' q'
    · rw [conj_triv hv p' q']
      have h := commute_conj huv (a ^ p * a' ^ q)
      rwa [conj_triv hv p q] at h
  · rw [conj_triv hu p q]
    have h := commute_conj huv (a ^ p' * a' ^ q')
    rwa [conj_triv hu p' q'] at h

/-! ### Exponent conditions -/

/-- At the coordinates `n ≥ m` the `a'`-exponents agree and the `a`-exponents differ by at
most one. -/
abbrev ExpCond (m : ℕ) (β γ β' γ' : Fin K → ℤ) : Prop :=
  ∀ n : Fin K, m ≤ n.val → γ n = γ' n ∧ -1 ≤ β' n - β n ∧ β' n - β n ≤ 1

theorem cond_self (m : ℕ) (β γ : Fin K → ℤ) : ExpCond m β γ β γ :=
  fun _ _ => ⟨rfl, by omega, by omega⟩

theorem cond_flip {m : ℕ} {β γ β' γ' : Fin K → ℤ} (h : ExpCond m β γ β' γ') :
    ExpCond m β' γ' β γ := by
  intro n hn
  obtain ⟨h0, h1, h2⟩ := h n hn
  exact ⟨h0.symm, by omega, by omega⟩

theorem cond_upd {m : ℕ} {β γ β' γ' : Fin K → ℤ} (h : ExpCond (m + 1) β γ β' γ')
    (k : Fin K) (hk : k.val = m) (p p' : ℤ) (hp : -1 ≤ p' - p ∧ p' - p ≤ 1) :
    ExpCond m (Function.update β k p) (Function.update γ k 0)
      (Function.update β' k p') (Function.update γ' k 0) := by
  intro n hn
  by_cases hnk : n = k
  · subst hnk
    rw [Function.update_self, Function.update_self, Function.update_self,
      Function.update_self]
    exact ⟨rfl, hp⟩
  · rw [Function.update_of_ne hnk, Function.update_of_ne hnk, Function.update_of_ne hnk,
      Function.update_of_ne hnk]
    have hne : n.val ≠ k.val := fun e => hnk (Fin.ext e)
    exact h n (by omega)

/-! ### Induction on the unconstrained coordinates -/

section Stage

variable (a a' : Fin K → G) {ι : Type*} (x : ι → G)

/-- The letters pairwise commute. -/
abbrev LComm : Prop :=
  ∀ n m, Commute (a n) (a m) ∧ Commute (a n) (a' m) ∧ Commute (a' n) (a' m)

/-- Each `x i` is active or inert at each coordinate. -/
abbrev XAct : Prop :=
  ∀ i n, a' n * x i * (a' n)⁻¹ = a n * x i * (a n)⁻¹ * (x i)⁻¹ ∨
    (Commute (x i) (a n) ∧ Commute (x i) (a' n))

/-- The base commutations. -/
abbrev XBase : Prop :=
  ∀ i j (β : Fin K → ℤ), (∀ n, -1 ≤ β n ∧ β n ≤ 1) →
    Commute ((pw a a' β 0)⁻¹ * x i * pw a a' β 0) (x j)

/-- Stage `m` of the induction. -/
abbrev Stage (m : ℕ) : Prop :=
  ∀ (i j : ι) (β γ β' γ' : Fin K → ℤ), ExpCond m β γ β' γ' →
    Commute ((pw a a' β γ)⁻¹ * x i * pw a a' β γ) ((pw a a' β' γ')⁻¹ * x j * pw a a' β' γ')

theorem pw_update_self (hl : LComm a a') (β γ : Fin K → ℤ) (k : Fin K) :
    pw a a' β γ = pw a a' (Function.update β k 0) (Function.update γ k 0)
      * (a k ^ β k * a' k ^ γ k) := by
  have h := pw_update a a' hl β γ k (β k) (γ k)
  rwa [Function.update_eq_self, Function.update_eq_self] at h

theorem pw_shift (hl : LComm a a') (β γ : Fin K → ℤ) (k : Fin K) :
    pw a a' (Function.update β k 1) (Function.update γ k 0)
      = pw a a' (Function.update β k 0) (Function.update γ k 0) * a k := by
  rw [pw_update a a' hl β γ k 1 0, zpow_one, zpow_zero, mul_one]

theorem stage_zero (hl : LComm a a') (hbase : XBase a a' x) : Stage a a' x 0 := by
  intro i j β γ β' γ' h
  have hγ : γ = γ' := funext fun n => (h n (Nat.zero_le _)).1
  have e : pw a a' β' γ' = pw a a' (β' - β) 0 * pw a a' β γ := by
    rw [pw_mul a a' hl, sub_add_cancel, zero_add, hγ]
  rw [e, conj_mul_eq (x j) (pw a a' (β' - β) 0) (pw a a' β γ)]
  exact commute_conj (hbase j i (β' - β) fun n => (h n (Nat.zero_le _)).2).symm _

theorem stage_succ (hl : LComm a a') (hact : XAct a a' x) {m : ℕ} (k : Fin K)
    (hk : k.val = m) (ih : Stage a a' x m) : Stage a a' x (m + 1) := by
  intro i j β γ β' γ' h
  have huv := ih i j (Function.update β k 0) (Function.update γ k 0)
    (Function.update β' k 0) (Function.update γ' k 0)
    (cond_upd h k hk 0 0 ⟨by omega, by omega⟩)
  have huu := ih i i (Function.update β k 0) (Function.update γ k 0)
    (Function.update β k 1) (Function.update γ k 0)
    (cond_upd (cond_self (m + 1) β γ) k hk 0 1 ⟨by omega, by omega⟩)
  have hvv := ih j j (Function.update β' k 0) (Function.update γ' k 0)
    (Function.update β' k 1) (Function.update γ' k 0)
    (cond_upd (cond_self (m + 1) β' γ') k hk 0 1 ⟨by omega, by omega⟩)
  have hu1 := ih i j (Function.update β k 0) (Function.update γ k 0)
    (Function.update β' k 1) (Function.update γ' k 0)
    (cond_upd h k hk 0 1 ⟨by omega, by omega⟩)
  have hv1 := ih j i (Function.update β' k 0) (Function.update γ' k 0)
    (Function.update β k 1) (Function.update γ k 0)
    (cond_upd (cond_flip h) k hk 0 1 ⟨by omega, by omega⟩)
  rw [pw_shift a a' hl β γ k,
    conj_mul_eq (x i) (pw a a' (Function.update β k 0) (Function.update γ k 0)) (a k)] at huu
  rw [pw_shift a a' hl β' γ' k,
    conj_mul_eq (x j) (pw a a' (Function.update β' k 0) (Function.update γ' k 0)) (a k)] at hvv
  rw [pw_shift a a' hl β' γ' k,
    conj_mul_eq (x j) (pw a a' (Function.update β' k 0) (Function.update γ' k 0)) (a k)] at hu1
  rw [pw_shift a a' hl β γ k,
    conj_mul_eq (x i) (pw a a' (Function.update β k 0) (Function.update γ k 0)) (a k)] at hv1
  rw [pw_update_self a a' hl β γ k, pw_update_self a a' hl β' γ' k,
    conj_mul_eq (x i) (pw a a' (Function.update β k 0) (Function.update γ k 0))
      (a k ^ β k * a' k ^ γ k),
    conj_mul_eq (x j) (pw a a' (Function.update β' k 0) (Function.update γ' k 0))
      (a k ^ β' k * a' k ^ γ' k)]
  have hQ : ∀ β₀ γ₀ : Fin K → ℤ,
      Commute (pw a a' β₀ γ₀) (a k) ∧ Commute (pw a a' β₀ γ₀) (a' k) := fun β₀ γ₀ =>
    ⟨(commute_pw a a' (fun n => ⟨(hl k n).1, (hl k n).2.1⟩) β₀ γ₀).symm,
      (commute_pw a a' (fun n => ⟨(hl n k).2.1.symm, (hl k n).2.2⟩) β₀ γ₀).symm⟩
  exact pair_commute (hl k k).2.1 huv huu hu1 hv1 hvv
    (act_conj (hQ (Function.update β k 0) (Function.update γ k 0)).1
      (hQ (Function.update β k 0) (Function.update γ k 0)).2 (hact i k))
    (act_conj (hQ (Function.update β' k 0) (Function.update γ' k 0)).1
      (hQ (Function.update β' k 0) (Function.update γ' k 0)).2 (hact j k))
    (β k) (γ k) (β' k) (γ' k)

theorem stage_all (hl : LComm a a') (hact : XAct a a' x) (hbase : XBase a a' x) (m : ℕ) :
    Stage a a' x m := by
  induction m with
  | zero => exact stage_zero a a' x hl hbase
  | succ m ih =>
    by_cases hmK : m < K
    · exact stage_succ a a' x hl hact ⟨m, hmK⟩ rfl ih
    · intro i j β γ β' γ' _
      apply ih i j β γ β' γ'
      intro n hn
      exact absurd (lt_of_le_of_lt hn n.isLt) hmK

end Stage

/-- **Lemma lBRG** (KMS, `p = 2`, multi-variable form): conjugates of the `x i` by products
`∏ a_n^{β_n} a_n'^{γ_n}` pairwise commute. -/
theorem multi_commute {ι : Type*} (a a' : Fin K → G) (x : ι → G)
    (hl : ∀ n m, Commute (a n) (a m) ∧ Commute (a n) (a' m) ∧ Commute (a' n) (a' m))
    (hact : ∀ i n, a' n * x i * (a' n)⁻¹ = a n * x i * (a n)⁻¹ * (x i)⁻¹ ∨
      (Commute (x i) (a n) ∧ Commute (x i) (a' n)))
    (hbase : ∀ i j (β : Fin K → ℤ), (∀ n, -1 ≤ β n ∧ β n ≤ 1) →
      Commute ((pw a a' β 0)⁻¹ * x i * pw a a' β 0) (x j))
    (i j : ι) (β γ β' γ' : Fin K → ℤ) :
    Commute ((pw a a' β γ)⁻¹ * x i * pw a a' β γ)
      ((pw a a' β' γ')⁻¹ * x j * pw a a' β' γ') :=
  stage_all a a' x hl hact hbase K i j β γ β' γ' fun n hn => absurd n.isLt (not_lt.mpr hn)

end BR
end KMS
end GroupApproximation.Full.Kharlampovich
