import GroupApproximation.ClassTransposition.Presentation.Decomp

/-!
# Realizations are invariants of `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
step O1, in `H P`).

* `real_eq_of_toH`: two valid words at level `n` with the same element of `H P` and the same final
  level have the same realization on every ordered partition of length `n`. Evaluate in `Perm ℤ`
  (`evalH_toH`), compare on the comb (`frac_inj`), and transport canonically (`forall₂_real`).
* `Eqv P n w w'`: the same element of `H P` and the same final level. It is a congruence for
  concatenation.
* `mapSwap_locS`: a swap word moves right past a split word acting to its right, unchanged.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- A permutation maps a box canonically onto at most one box. -/
theorem canonOn_unique {g : Perm ℤ} {A B C : Box} (h1 : CanonOn g A B) (h2 : CanonOn g A C) :
    B = C := by
  have e0 := (h1 0).symm.trans (h2 0)
  have e1 := (h1 1).symm.trans (h2 1)
  simp only [zero_mul, add_zero, one_mul] at e0 e1
  exact Box.ext e0 (by linarith)

theorem forall₂_unique {g : Perm ℤ} {a b c : List Box} (h1 : List.Forall₂ (CanonOn g) a b)
    (h2 : List.Forall₂ (CanonOn g) a c) : b = c := by
  induction h1 generalizing c with
  | nil => cases h2; rfl
  | cons h t ih => cases h2 with | cons h' t' => rw [canonOn_unique h h', ih t']

/-- `frac b` is injective on ordered partitions of the length of `b`. -/
theorem frac_inj {b c c' : List Box} (hb : IsPart b) (hc : IsPart c) (hc' : IsPart c')
    (hl : b.length = c.length) (hl' : b.length = c'.length) (h : frac b c = frac b c') :
    c = c' := by
  have h2 := frac_canon hb hc' hl'
  rw [← h] at h2
  exact forall₂_unique (frac_canon hb hc hl) h2

/-- **Realization is an invariant.** -/
theorem real_eq_of_toH (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) {n : ℕ} (hn : 0 < n)
    {w w' : List Move} (hw : ValW P n w) (hw' : ValW P n w') (hl : levW n w = levW n w')
    (h : toH P n w = toH P n w') {b : List Box} (hb : IsPart b) (hbn : b.length = n) :
    real b w = real b w' := by
  have e := congrArg (evalH hpos hP2) h
  rw [evalH_toH hpos hP2 hn hw, evalH_toH hpos hP2 hn hw', hl] at e
  have hc := frac_inj (isPart_comb _ (lt_of_lt_of_le hn (levW_ge n w' (ValW.ok hpos hw'))))
    (isPart_real (isPart_comb n hn) w (ValW.ok hpos hw))
    (isPart_real (isPart_comb n hn) w' (ValW.ok hpos hw'))
    (by rw [length_comb, length_real, length_comb, hl])
    (by rw [length_comb, length_real, length_comb]) e
  have g := frac_canon (isPart_comb n hn) hb (by rw [length_comb, hbn])
  have h1 := forall₂_real g w
  have h2 := forall₂_real g w'
  rw [hc] at h1
  exact forall₂_unique h1 h2

/-! ### The congruence `Eqv` -/

/-- The same element of `H P` and the same final level. -/
def Eqv (P : Set ℕ) (n : ℕ) (w w' : List Move) : Prop :=
  toH P n w = toH P n w' ∧ levW n w = levW n w'

theorem Eqv.refl (n : ℕ) (w : List Move) : Eqv P n w w := ⟨rfl, rfl⟩

theorem Eqv.of_eq {n : ℕ} {w w' : List Move} (h : w = w') : Eqv P n w w' := by
  subst h; exact Eqv.refl n w

theorem Eqv.symm {n : ℕ} {w w' : List Move} (h : Eqv P n w w') : Eqv P n w' w :=
  ⟨h.1.symm, h.2.symm⟩

theorem Eqv.trans {n : ℕ} {u v w : List Move} (h1 : Eqv P n u v) (h2 : Eqv P n v w) :
    Eqv P n u w :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem Eqv.append_right {n : ℕ} {u u' : List Move} (h : Eqv P n u u') (w : List Move) :
    Eqv P n (u ++ w) (u' ++ w) :=
  ⟨toH_prefix h.1 h.2 w, by rw [levW_append, levW_append, h.2]⟩

theorem Eqv.append_left {n : ℕ} (u : List Move) {w w' : List Move}
    (h : Eqv P (levW n u) w w') : Eqv P n (u ++ w) (u ++ w') :=
  ⟨by rw [toH_append, toH_append, h.1], by rw [levW_append, levW_append, h.2]⟩

theorem Eqv.cons {n : ℕ} (m : Move) {w w' : List Move} (h : Eqv P (m.lev n) w w') :
    Eqv P n (m :: w) (m :: w') :=
  Eqv.append_left [m] h

theorem Eqv.real_eq (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) {n : ℕ} (hn : 0 < n)
    {w w' : List Move} (h : Eqv P n w w') (hw : ValW P n w) (hw' : ValW P n w')
    {b : List Box} (hb : IsPart b) (hbn : b.length = n) : real b w = real b w' :=
  real_eq_of_toH hpos hP2 hn hw hw' h.2 h.1 hb hbn

/-! ### Validity from locality -/

theorem valW_of_locB (hpos : ∀ p ∈ P' P, 2 ≤ p) (lo : ℕ) : ∀ (w : List Move) (n hi : ℕ),
    hi ≤ n → LocB lo hi w → PrimesIn P w → ValW P n w
  | [], _, _, _, _, _ => trivial
  | .split i p :: w, n, hi, hn, ⟨_, h2, h3⟩, ⟨hp, hw⟩ => by
    have := hpos p hp
    refine ⟨⟨by omega, hp⟩, ?_⟩
    rw [lev_split p (by omega)]
    exact valW_of_locB hpos lo w (n + p - 1) (hi + (p - 1)) (by omega) h3 hw
  | .swap k :: w, n, hi, hn, ⟨_, h2, h3⟩, hw =>
    ⟨show k + 1 < n by omega, valW_of_locB hpos lo w n hi hn h3 hw⟩

theorem locB_of_valW (hpos : ∀ p ∈ P' P, 2 ≤ p) : ∀ (n : ℕ) (w : List Move), ValW P n w →
    LocB 0 n w ∧ PrimesIn P w
  | _, [], _ => ⟨trivial, trivial⟩
  | n, .split i p :: w, ⟨⟨h1, hp⟩, hw⟩ => by
    have := hpos p hp
    rw [lev_split p h1] at hw
    obtain ⟨a, b⟩ := locB_of_valW hpos (n + p - 1) w hw
    exact ⟨⟨Nat.zero_le _, h1, by rwa [show n + (p - 1) = n + p - 1 by omega]⟩, hp, b⟩
  | n, .swap k :: w, ⟨h1, hw⟩ => by
    obtain ⟨a, b⟩ := locB_of_valW hpos n w hw
    exact ⟨⟨Nat.zero_le _, h1, a⟩, b⟩

/-- A word acting inside a block that starts at the level: `Eqv` from `toH`. -/
theorem eqv_of_toH (hpos : ∀ p ∈ P' P, 2 ≤ p) (lo : ℕ) {w w' : List Move} {n hi : ℕ} (hn : hi ≤ n)
    (hw : LocB lo hi w) (hw' : LocB lo hi w') (hpw : PrimesIn P w) (hpw' : PrimesIn P w')
    (hg : growth w = growth w') (h : toH P n w = toH P n w') : Eqv P n w w' :=
  ⟨h, by rw [levW_locB hpos lo w n hi hn hw hpw, levW_locB hpos lo w' n hi hn hw' hpw', hg]⟩

/-! ### Swap words commute with split words to their right -/

section Comm

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

theorem mapSwap_split {i p : ℕ} (hp : p ∈ P' P) : ∀ (σ : List ℕ) (n : ℕ), i < n →
    (∀ k ∈ σ, k + 1 < i) →
    Eqv P n (σ.map Move.swap ++ [.split i p]) (.split i p :: σ.map Move.swap)
  | [], n, _, _ => Eqv.refl n _
  | k :: σ, n, hi, hσ => by
    have hk := hσ k List.mem_cons_self
    have ih := mapSwap_split hp σ n hi fun k' hk' => hσ k' (List.mem_cons_of_mem _ hk')
    have e2 : Eqv P n [.swap k, .split i p] [.split i p, .swap k] :=
      ⟨dr_all hB hP2 hpos (by omega) hi hp,
        by simp only [levW_cons, levW_nil, lev_swap, lev_split p hi]⟩
    exact (Eqv.cons (.swap k) ih).trans (e2.append_right (σ.map Move.swap))

/-- A swap word moves right past a split word acting to its right. -/
theorem mapSwap_locS (f : ℕ) : ∀ (C : List Move) (σ : List ℕ) (n h : ℕ), h ≤ n → LocS f h C →
    PrimesIn P C → (∀ k ∈ σ, k + 1 < f) →
    Eqv P n (σ.map Move.swap ++ C) (C ++ σ.map Move.swap)
  | [], σ, n, _, _, _, _, _ => by rw [List.append_nil, List.nil_append]; exact Eqv.refl n _
  | .swap _ :: _, _, _, _, _, hC, _, _ => (show False from hC).elim
  | .split i p :: C, σ, n, h, hn, ⟨h1, h2, hC⟩, ⟨hp, hpC⟩, hσ => by
    have hp1 := hpos p hp
    have e1 := (mapSwap_split hB hP2 hpos (i := i) hp σ n (by omega) fun k hk => by
      have := hσ k hk; omega).append_right C
    have e2 := mapSwap_locS f C σ (n + p - 1) (h + (p - 1)) (by omega) hC hpC hσ
    have e3 : Eqv P n (.split i p :: (σ.map Move.swap ++ C))
        (.split i p :: (C ++ σ.map Move.swap)) :=
      Eqv.cons _ (by rw [lev_split p (by omega)]; exact e2)
    rw [List.append_assoc] at e1
    exact e1.trans e3

theorem swaps_locS (f : ℕ) (C : List Move) (σ : List ℕ) (n h : ℕ) (hn : h ≤ n) (hC : LocS f h C)
    (hpC : PrimesIn P C) (hσ : ∀ k ∈ σ, k + 1 < f) : Eqv P n (swaps 0 σ ++ C) (C ++ swaps 0 σ) := by
  rw [swaps_zero]
  exact mapSwap_locS hB hP2 hpos f C σ n h hn hC hpC hσ

end Comm

end GroupApproximation.ClassTransposition.Presentation
