import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Push

/-!
# Relative property (T): valuation combinatorics of characters of `F_p[X]²`

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's Kazhdan group
uses relative property (T) of `(F_p[t,t⁻¹]^3 ⋊ SL_3, F_p[t,t⁻¹]^3)` (A. Thom, Groups Geom. Dyn. 4
(2010), §2.1, Lemma 2.1).  In Burger's argument (Burger 1991; Shalom 1999; Kassabov 2007, §2) a
character `χ` of the plane `F_p[X]²` is recorded by the two sequences `λ n = χ(Xⁿ, 0)` and
`μ n = χ(0, Xⁿ)`.  The shears act on these sequences by
`μ n ↦ λ (n+1) · μ n` (shear by `X`) and `μ n ↦ λ n · μ n` (shear by `1`), and symmetrically.

This file is the purely combinatorial part.  For two sequences `f g : ℕ → ℂ`:

* `SeqD f g`: `f 0 ≠ 1` or `g 0 ≠ 1` (the scalar region);
* `SeqA f g`: both start at `1` and the first nontrivial index of `f` is strictly smaller than that
  of `g`;
* `SeqB f g`: both start at `1` and have the same first nontrivial index.

The main results are the shift placements `upShift_of_A`, `upShift_of_B`, `bp_of_ap`, the
disjointness lemmas, the covering lemma `cover`, and `polyTrivial`: an additive character of
`F_p[X]` that is trivial on all monomials `Xⁿ` is trivial.
-/

namespace GroupApproximation.Full.A2ThomT

namespace RelTSeq

/-- `k` is the first index at which `f` differs from `1`. -/
abbrev SeqVal (f : ℕ → ℂ) (k : ℕ) : Prop :=
  (∀ n < k, f n = 1) ∧ f k ≠ 1

/-- The scalar region: one of the sequences is nontrivial at index `0`. -/
abbrev SeqD (f g : ℕ → ℂ) : Prop :=
  f 0 ≠ 1 ∨ g 0 ≠ 1

/-- The region where `f` becomes nontrivial strictly before `g`. -/
abbrev SeqA (f g : ℕ → ℂ) : Prop :=
  f 0 = 1 ∧ g 0 = 1 ∧ ∃ k, SeqVal f k ∧ ∀ n ≤ k, g n = 1

/-- The region where `f` and `g` become nontrivial at the same index. -/
abbrev SeqB (f g : ℕ → ℂ) : Prop :=
  f 0 = 1 ∧ g 0 = 1 ∧ ∃ k, SeqVal f k ∧ SeqVal g k

theorem val_unique {f : ℕ → ℂ} {k l : ℕ} (hk : SeqVal f k) (hl : SeqVal f l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact absurd (hl.1 k h) hk.2
  · exact h
  · exact absurd (hk.1 l h) hl.2

theorem bp_symm {f g : ℕ → ℂ} (h : SeqB f g) : SeqB g f := by
  obtain ⟨hf0, hg0, k, hf, hg⟩ := h
  exact ⟨hg0, hf0, k, hg, hf⟩

theorem dp_symm {f g : ℕ → ℂ} (h : SeqD f g) : SeqD g f :=
  Or.symm h

theorem not_ap_and_bp {f g : ℕ → ℂ} (hA : SeqA f g) (hB : SeqB f g) : False := by
  obtain ⟨_, _, k, hk, hg⟩ := hA
  obtain ⟨_, _, l, hl, hl'⟩ := hB
  have hkl : k = l := val_unique hk hl
  subst hkl
  exact hl'.2 (hg k le_rfl)

/-- The core of the shift placement: if `f` starts at `1` with first nontrivial index `j + 1` and
`g` is trivial up to `j`, then after the shear `g ↦ f (· + 1) · g` the pair lands in `A`
(with the roles swapped) or in the scalar region. -/
theorem core {f g : ℕ → ℂ} {j : ℕ} (hf0 : f 0 = 1) (hval : SeqVal f (j + 1))
    (hg : ∀ n ≤ j, g n = 1) :
    SeqA (fun n ↦ f (n + 1) * g n) f ∨ SeqD f (fun n ↦ f (n + 1) * g n) := by
  have hval' : ∀ n < j, f (n + 1) * g n = 1 := by
    intro n hn
    rw [hval.1 (n + 1) (by omega), hg n hn.le, one_mul]
  have hj : f (j + 1) * g j ≠ 1 := by
    rw [hg j le_rfl, mul_one]
    exact hval.2
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    right
    right
    exact hj
  · left
    exact ⟨hval' 0 hjpos, hf0, j, ⟨hval', hj⟩, fun n hn ↦ hval.1 n (by omega)⟩

/-- Shear by `X` on the region `A`. -/
theorem upShift_of_A {f g : ℕ → ℂ} (h : SeqA f g) :
    SeqA (fun n ↦ f (n + 1) * g n) f ∨ SeqD f (fun n ↦ f (n + 1) * g n) := by
  obtain ⟨hf0, _, k, hval, hg⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hval.2 hf0
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
  exact core hf0 hval fun n hn ↦ hg n (by omega)

/-- Shear by `X` on the region `B`. -/
theorem upShift_of_B {f g : ℕ → ℂ} (h : SeqB f g) :
    SeqA (fun n ↦ f (n + 1) * g n) f ∨ SeqD f (fun n ↦ f (n + 1) * g n) := by
  obtain ⟨hf0, _, k, hval, hgval⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hval.2 hf0
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
  exact core hf0 hval fun n hn ↦ hgval.1 n (by omega)

/-- Shear by `1` maps the region `A` into the region `B`. -/
theorem bp_of_ap {f g : ℕ → ℂ} (h : SeqA f g) : SeqB f (fun n ↦ f n * g n) := by
  obtain ⟨hf0, hg0, k, hval, hg⟩ := h
  refine ⟨hf0, ?_, k, hval, fun n hn ↦ ?_, ?_⟩
  · show f 0 * g 0 = 1
    rw [hf0, hg0, one_mul]
  · show f n * g n = 1
    rw [hval.1 n hn, hg n hn.le, one_mul]
  · show f k * g k ≠ 1
    rw [hg k le_rfl, mul_one]
    exact hval.2

/-- Every pair of sequences with a nontrivial entry lies in one of the four regions. -/
theorem cover {f g : ℕ → ℂ} (h : ∃ n, f n ≠ 1 ∨ g n ≠ 1) :
    SeqA f g ∨ SeqB f g ∨ SeqA g f ∨ SeqD f g := by
  classical
  by_cases hd : f 0 = 1 ∧ g 0 = 1
  · obtain ⟨k, hk, hmin⟩ :
        ∃ k, (f k ≠ 1 ∨ g k ≠ 1) ∧ ∀ n < k, f n = 1 ∧ g n = 1 := by
      refine ⟨Nat.find h, Nat.find_spec h, fun n hn ↦ ?_⟩
      have hnot := Nat.find_min h hn
      push_neg at hnot
      exact hnot
    have hup : ∀ u : ℕ → ℂ, (∀ n < k, u n = 1) → u k = 1 → ∀ n ≤ k, u n = 1 := by
      intro u hlt hkk n hn
      rcases Nat.lt_or_eq_of_le hn with hnk | hnk
      · exact hlt n hnk
      · rw [hnk]
        exact hkk
    by_cases hfk : f k = 1
    · have hgk : g k ≠ 1 := by
        rcases hk with hk | hk
        · exact absurd hfk hk
        · exact hk
      exact Or.inr (Or.inr (Or.inl ⟨hd.2, hd.1, k, ⟨fun n hn ↦ (hmin n hn).2, hgk⟩,
        hup f (fun n hn ↦ (hmin n hn).1) hfk⟩))
    · by_cases hgk : g k = 1
      · exact Or.inl ⟨hd.1, hd.2, k, ⟨fun n hn ↦ (hmin n hn).1, hfk⟩,
          hup g (fun n hn ↦ (hmin n hn).2) hgk⟩
      · exact Or.inr (Or.inl ⟨hd.1, hd.2, k, ⟨fun n hn ↦ (hmin n hn).1, hfk⟩,
          ⟨fun n hn ↦ (hmin n hn).2, hgk⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (not_and_or.mp hd)))

/-- An additive character of `F_p[X]` that is trivial on every monomial `Xⁿ` is trivial. -/
theorem polyTrivial {p : ℕ} [NeZero p] (ψ : Polynomial (ZMod p) → ℂ)
    (hadd : ∀ a b, ψ (a + b) = ψ a * ψ b) (hzero : ψ 0 = 1)
    (hX : ∀ n : ℕ, ψ (Polynomial.X ^ n) = 1) (a : Polynomial (ZMod p)) : ψ a = 1 := by
  induction a using Polynomial.induction_on' with
  | add q r hq hr => rw [hadd, hq, hr, one_mul]
  | monomial n c =>
    have hnat : ∀ m : ℕ, ψ (Polynomial.monomial n (m : ZMod p)) = 1 := by
      intro m
      induction m with
      | zero => rw [Nat.cast_zero, map_zero, hzero]
      | succ m ih =>
        rw [Nat.cast_succ, map_add, hadd, ih, ← Polynomial.X_pow_eq_monomial, hX, one_mul]
    rw [← ZMod.natCast_zmod_val c]
    exact hnat c.val

end RelTSeq

end GroupApproximation.Full.A2ThomT
