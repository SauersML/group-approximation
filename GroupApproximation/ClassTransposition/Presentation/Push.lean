import GroupApproximation.ClassTransposition.Presentation.EvalRel

/-!
# Moving moves past each other in `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1, Fact O
step O1, in `H P`).

* `push_split`: a split moves to the right past a split word acting to its left.
* `swaps_split`: a split moves to the left past a swap word, turning it into another swap word.
* `exists_split_swaps`: every valid word equals a split word followed by a swap word.

All three stay inside a block of boxes when the words do.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem toH_prefix {n : ℕ} {u u' : List Move} (h : toH P n u = toH P n u')
    (hl : levW n u = levW n u') (w : List Move) : toH P n (u ++ w) = toH P n (u' ++ w) := by
  rw [toH_append, toH_append, h, hl]

/-- The split word acts strictly left of position `j` (which moves right as it splits). -/
def LeftOf : ℕ → List Move → Prop
  | _, [] => True
  | j, .split i p :: w => i < j ∧ LeftOf (j + p - 1) w
  | _, .swap _ :: _ => False

/-- Where position `j` ends up after a split word acting to its left. -/
def shiftPos : ℕ → List Move → ℕ
  | j, [] => j
  | j, .split _ p :: w => shiftPos (j + p - 1) w
  | j, .swap _ :: _ => j

/-- Every split in the word is by a prime of `P ∪ {2}`. -/
def PrimesIn (P : Set ℕ) : List Move → Prop
  | [] => True
  | .split _ p :: w => p ∈ P' P ∧ PrimesIn P w
  | .swap _ :: w => PrimesIn P w

/-- The number of boxes a word adds. -/
def growth : List Move → ℕ
  | [] => 0
  | .split _ p :: w => p - 1 + growth w
  | .swap _ :: w => growth w

/-- The word acts inside the block `[lo, hi)` (which grows with the splits). -/
def LocB (lo : ℕ) : ℕ → List Move → Prop
  | _, [] => True
  | hi, .split i p :: w => lo ≤ i ∧ i < hi ∧ LocB lo (hi + (p - 1)) w
  | hi, .swap k :: w => lo ≤ k ∧ k + 1 < hi ∧ LocB lo hi w

/-- A split word acting inside the block `[lo, hi)`. -/
def LocS (lo : ℕ) : ℕ → List Move → Prop
  | _, [] => True
  | hi, .split i p :: w => lo ≤ i ∧ i < hi ∧ LocS lo (hi + (p - 1)) w
  | _, .swap _ :: _ => False

theorem locB_append (lo : ℕ) : ∀ (hi : ℕ) (u v : List Move),
    LocB lo hi (u ++ v) ↔ LocB lo hi u ∧ LocB lo (hi + growth u) v
  | hi, [], v => by simp [LocB, growth]
  | hi, .split i p :: u, v => by
    show (lo ≤ i ∧ i < hi ∧ LocB lo (hi + (p - 1)) (u ++ v)) ↔
      (lo ≤ i ∧ i < hi ∧ LocB lo (hi + (p - 1)) u) ∧ LocB lo (hi + (p - 1 + growth u)) v
    rw [locB_append lo (hi + (p - 1)) u v]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨h1, h2, h3⟩, ?_⟩
      convert h4 using 1; omega
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, h3, ?_⟩
      convert h4 using 1; omega
  | hi, .swap k :: u, v => by
    show (lo ≤ k ∧ k + 1 < hi ∧ LocB lo hi (u ++ v)) ↔
      (lo ≤ k ∧ k + 1 < hi ∧ LocB lo hi u) ∧ LocB lo (hi + growth u) v
    rw [locB_append lo hi u v]
    tauto

theorem locS_append (lo : ℕ) : ∀ (hi : ℕ) (u v : List Move),
    LocS lo hi (u ++ v) ↔ LocS lo hi u ∧ LocS lo (hi + growth u) v
  | hi, [], v => by simp [LocS, growth]
  | hi, .split i p :: u, v => by
    show (lo ≤ i ∧ i < hi ∧ LocS lo (hi + (p - 1)) (u ++ v)) ↔
      (lo ≤ i ∧ i < hi ∧ LocS lo (hi + (p - 1)) u) ∧ LocS lo (hi + (p - 1 + growth u)) v
    rw [locS_append lo (hi + (p - 1)) u v]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨h1, h2, h3⟩, ?_⟩
      convert h4 using 1; omega
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, h3, ?_⟩
      convert h4 using 1; omega
  | hi, .swap _ :: _, _ => by simp [LocS]

theorem primesIn_append : ∀ u v : List Move, PrimesIn P (u ++ v) ↔ PrimesIn P u ∧ PrimesIn P v
  | [], v => by simp [PrimesIn]
  | .split _ p :: u, v => by
    show (p ∈ P' P ∧ PrimesIn P (u ++ v)) ↔ (p ∈ P' P ∧ PrimesIn P u) ∧ PrimesIn P v
    rw [primesIn_append u v, and_assoc]
  | .swap _ :: u, v => primesIn_append u v

/-- A word acting inside a block that starts at the level adds `growth` boxes. -/
theorem levW_locB (hpos : ∀ p ∈ P' P, 2 ≤ p) (lo : ℕ) : ∀ (w : List Move) (n hi : ℕ), hi ≤ n → LocB lo hi w →
    PrimesIn P w → levW n w = n + growth w
  | [], _, _, _, _, _ => rfl
  | .split i p :: w, n, hi, hn, ⟨_, h2, h3⟩, ⟨hp, hw⟩ => by
    have := hpos p hp
    rw [levW_cons, lev_split p (by omega),
      levW_locB hpos lo w (n + p - 1) (hi + (p - 1)) (by omega) h3 hw]
    simp only [growth]
    omega
  | .swap _ :: w, n, hi, hn, ⟨_, _, h3⟩, hw => levW_locB hpos lo w n hi hn h3 hw

theorem levW_append : ∀ (n : ℕ) (u v : List Move), levW n (u ++ v) = levW (levW n u) v
  | _, [], _ => rfl
  | n, m :: u, v => levW_append (m.lev n) u v

theorem growth_append : ∀ u v : List Move, growth (u ++ v) = growth u + growth v
  | [], v => (zero_add _).symm
  | .split _ p :: u, v => by
    show p - 1 + growth (u ++ v) = p - 1 + growth u + growth v
    rw [growth_append u v, add_assoc]
  | .swap _ :: u, v => growth_append u v

theorem locB_of_locS {lo : ℕ} : ∀ {hi : ℕ} {w : List Move}, LocS lo hi w → LocB lo hi w
  | _, [], _ => trivial
  | _, .split _ _ :: _, ⟨h1, h2, h3⟩ => ⟨h1, h2, locB_of_locS h3⟩
  | _, .swap _ :: _, h => (show False from h).elim

theorem swaps_zero (w : List ℕ) : swaps 0 w = w.map Move.swap := by
  simp [swaps]

theorem levW_swaps0 (n : ℕ) (w : List ℕ) : levW n (swaps 0 w) = n := levW_swaps 0 n w

theorem locB_swaps {lo hi : ℕ} : ∀ σ : List ℕ, (∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi) →
    LocB lo hi (swaps 0 σ)
  | [], _ => trivial
  | k :: σ, h => ⟨by have := (h k List.mem_cons_self).1; simpa using this,
      by have := (h k List.mem_cons_self).2; simpa using this,
      locB_swaps σ fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

theorem growth_swaps : ∀ σ : List ℕ, growth (swaps 0 σ) = 0
  | [] => rfl
  | _ :: σ => growth_swaps σ

section Push

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

/-- A split moves right past a split word acting to its left. -/
theorem push_split {q : ℕ} (hq : q ∈ P' P) : ∀ (A : List Move) (n j : ℕ), j < n → LeftOf j A →
    PrimesIn P A → toH P n (.split j q :: A) = toH P n (A ++ [.split (shiftPos j A) q])
  | [], _, _, _, _, _ => rfl
  | .swap _ :: _, _, _, _, h, _ => (show False from h).elim
  | .split i p :: A, n, j, hj, ⟨hij, hA⟩, ⟨hp, hPA⟩ => by
    have hp1 := hpos p hp
    have hq1 := hpos q hq
    have e := fsp_all hB hP2 hpos (n := n) hij hj hp hq
    have el : levW n [.split j q, .split i p] = levW n [.split i p, .split (j + p - 1) q] := by
      simp only [levW_cons, levW_nil, lev_split q hj, lev_split p (show i < n + q - 1 by omega),
        lev_split p (show i < n by omega), lev_split q (show j + p - 1 < n + p - 1 by omega)]
      omega
    have h1 := toH_prefix e.symm el A
    simp only [List.cons_append, List.nil_append] at h1
    rw [h1, toH_cons, lev_split p (show i < n by omega),
      push_split hq A (n + p - 1) (j + p - 1) (by omega) hA hPA, List.cons_append, toH_cons,
      lev_split p (show i < n by omega)]
    rfl

/-- A split moves left past a swap word inside a block `[lo, hi)`, which becomes another swap
word inside the enlarged block. -/
theorem swaps_split {p : ℕ} (hp : p ∈ P' P) (lo : ℕ) : ∀ (σ : List ℕ) (n hi i : ℕ), hi ≤ n →
    (∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi) → lo ≤ i → i < hi →
    ∃ i' σ', lo ≤ i' ∧ i' < hi ∧ (∀ k ∈ σ', lo ≤ k ∧ k + 1 < hi + p - 1) ∧
      toH P n (swaps 0 σ ++ [.split i p]) = toH P n (.split i' p :: swaps 0 σ') := by
  have hp1 := hpos p hp
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro n hi i _ _ hlo hi'
    exact ⟨i, [], hlo, hi', by simp, by simp [swaps]⟩
  | append_singleton σ k ih =>
    intro n hi i hn hσ hlo hi'
    have hk := hσ k (List.mem_append_right _ List.mem_cons_self)
    have hσ' : ∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi := fun k' hk' => hσ k' (List.mem_append_left _ hk')
    -- one step: `[swap k, split i p] = split i₁ p :: swaps 0 τ`
    obtain ⟨i₁, τ, h1, h2, hτ, e1⟩ : ∃ i₁ τ, lo ≤ i₁ ∧ i₁ < hi ∧
        (∀ k ∈ τ, lo ≤ k ∧ k + 1 < hi + p - 1) ∧
        toH P n [.swap k, .split i p] = toH P n (.split i₁ p :: swaps 0 τ) := by
      rcases Nat.lt_trichotomy i k with h | rfl | h
      · refine ⟨i, [k + p - 1], hlo, hi', by simp; omega, ?_⟩
        rw [dl_all hB hP2 hpos h (by omega) hp]; simp [swaps]
      · refine ⟨i + 1, (List.range p).map (i + ·), by omega, by omega, ?_, ?_⟩
        · intro t ht
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht
          rw [List.mem_range] at ht; omega
        · rw [dk_all hB hp n i (by omega)]
          simp [swaps, Function.comp_def]
      · rcases Nat.lt_or_ge (k + 1) i with h' | h'
        · refine ⟨i, [k], hlo, hi', by simp; omega, ?_⟩
          rw [dr_all hB hP2 hpos h' (by omega) hp]; simp [swaps]
        · have hik : i = k + 1 := by omega
          subst hik
          refine ⟨k, (List.range p).reverse.map (k + ·), hk.1, by omega, ?_, ?_⟩
          · intro t ht
            obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht
            rw [List.mem_reverse, List.mem_range] at ht; omega
          · rw [dk1_all hB hp n k (by omega)]
            simp [swaps, Function.comp_def]
    obtain ⟨i', σ', h3, h4, hσ'', e2⟩ := ih n hi i₁ hn hσ' h1 h2
    refine ⟨i', σ' ++ τ, h3, h4, ?_, ?_⟩
    · intro k' hk'
      rcases List.mem_append.1 hk' with hk' | hk'
      · exact hσ'' k' hk'
      · exact hτ k' hk'
    · have ls : ∀ w : List ℕ, levW n (swaps 0 w) = n := fun w => levW_swaps 0 n w
      calc toH P n (swaps 0 (σ ++ [k]) ++ [.split i p])
          = toH P n (swaps 0 σ) * toH P n [.swap k, .split i p] := by
            rw [show swaps 0 (σ ++ [k]) ++ [Move.split i p] = swaps 0 σ ++ [.swap k, .split i p] by
              simp [swaps], toH_append, ls]
        _ = toH P n (swaps 0 σ) * toH P n [.split i₁ p] * toH P (n + p - 1) (swaps 0 τ) := by
            rw [e1, show (Move.split i₁ p :: swaps 0 τ) = [.split i₁ p] ++ swaps 0 τ from rfl,
              toH_append, levW_cons, levW_nil, lev_split p (show i₁ < n by omega), mul_assoc]
        _ = toH P n (swaps 0 σ ++ [.split i₁ p]) * toH P (n + p - 1) (swaps 0 τ) := by
            rw [toH_append, ls]
        _ = toH P n (.split i' p :: swaps 0 σ') * toH P (n + p - 1) (swaps 0 τ) := by rw [e2]
        _ = toH P n (.split i' p :: swaps 0 (σ' ++ τ)) := by
            rw [show swaps 0 (σ' ++ τ) = swaps 0 σ' ++ swaps 0 τ by simp [swaps], ← List.cons_append,
              toH_append, levW_cons, lev_split p (show i' < n by omega), levW_swaps]

/-- Every word acting inside a block is a split word followed by a swap word, both inside the
block. -/
theorem exists_split_swaps (lo : ℕ) : ∀ (w : List Move) (n hi : ℕ), hi ≤ n → LocB lo hi w →
    PrimesIn P w → ∃ t σ, LocS lo hi t ∧ PrimesIn P t ∧ growth t = growth w ∧
      (∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi + growth w) ∧ toH P n w = toH P n (t ++ swaps 0 σ) := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro n hi _ _ _; exact ⟨[], [], trivial, trivial, rfl, by simp, by simp [swaps]⟩
  | append_singleton w m ih =>
    intro n hi hn hloc hpr
    obtain ⟨hw, hm⟩ := (locB_append lo hi w [m]).1 hloc
    obtain ⟨hpw, hpm⟩ := (primesIn_append w [m]).1 hpr
    obtain ⟨t, σ, ht, hpt, hg, hσ, e⟩ := ih n hi hn hw hpw
    have lw : levW n w = n + growth w := levW_locB hpos lo w n hi hn hw hpw
    have lt : levW n t = n + growth t := levW_locB hpos lo t n hi hn (locB_of_locS ht) hpt
    have ltσ : levW n (t ++ swaps 0 σ) = n + growth w := by
      rw [levW_append, levW_swaps0, lt, hg]
    cases m with
    | swap k =>
      obtain ⟨h1, h2, -⟩ := hm
      refine ⟨t, σ ++ [k], ht, hpt, by rw [hg, growth_append]; rfl, ?_, ?_⟩
      · intro k' hk'
        rw [growth_append]
        rcases List.mem_append.1 hk' with hk' | hk'
        · have := hσ k' hk'; exact ⟨this.1, by simp only [growth]; omega⟩
        · rw [List.mem_singleton] at hk'; subst hk'; exact ⟨h1, by simp only [growth]; omega⟩
      · rw [toH_append, e, lw, ← ltσ, ← toH_append, swaps_zero, swaps_zero, List.map_append,
          List.append_assoc]
        rfl
    | split i p =>
      obtain ⟨h1, h2, -⟩ := hm
      obtain ⟨hp, -⟩ := hpm
      have hp1 := hpos p hp
      obtain ⟨i', σ', h3, h4, hσ', e2⟩ := swaps_split hB hP2 hpos hp lo σ (n + growth t)
        (hi + growth t) i (by omega) (fun k hk => by rw [hg]; exact hσ k hk) h1 (by rw [hg]; exact h2)
      refine ⟨t ++ [.split i' p], σ', ?_, ?_, ?_, ?_, ?_⟩
      · exact (locS_append lo hi t _).2 ⟨ht, h3, h4, trivial⟩
      · exact (primesIn_append t _).2 ⟨hpt, hp, trivial⟩
      · rw [growth_append, growth_append, hg]; rfl
      · intro k hk
        have := hσ' k hk
        rw [growth_append]
        simp only [growth]
        omega
      · calc toH P n (w ++ [.split i p])
            = toH P n w * toH P (n + growth w) [.split i p] := by rw [toH_append, lw]
          _ = toH P n t * toH P (n + growth t) (swaps 0 σ) * toH P (n + growth t) [.split i p] := by
            rw [e, toH_append n t (swaps 0 σ), lt, hg]
          _ = toH P n t * toH P (n + growth t) (swaps 0 σ ++ [.split i p]) := by
            rw [toH_append (n + growth t) (swaps 0 σ) [.split i p], levW_swaps0, mul_assoc]
          _ = toH P n t * toH P (n + growth t) (.split i' p :: swaps 0 σ') := by rw [e2]
          _ = toH P n ((t ++ [.split i' p]) ++ swaps 0 σ') := by
            rw [List.append_assoc, List.singleton_append, toH_append n t, lt]

end Push

end GroupApproximation.ClassTransposition.Presentation
