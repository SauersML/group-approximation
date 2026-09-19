import GroupApproximation.ClassTransposition.Presentation.Push

/-!
# Splitting a split word into its trees

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O step
O1, in `H P`).

A split word acting on a block `[o, h)` equals, in `H P`, a split word acting only on the first
part `[o, f)` followed by one acting only on the rest (`decomp`). The moves on the rest are moved
right past the moves on the first part by `push_split`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem leftOf_of_locS (hpos : ∀ p ∈ P' P, 2 ≤ p) {o : ℕ} : ∀ {f j : ℕ} {A : List Move},
    LocS o f A → PrimesIn P A → f ≤ j → LeftOf j A
  | _, _, [], _, _, _ => trivial
  | f, j, .split i p :: A, ⟨_, h2, h3⟩, ⟨hp, hA⟩, hfj => by
    have := hpos p hp
    exact ⟨by omega, leftOf_of_locS hpos h3 hA (by omega)⟩
  | _, _, .swap _ :: _, h, _, _ => (show False from h).elim

theorem shiftPos_eq (hpos : ∀ p ∈ P' P, 2 ≤ p) : ∀ (j : ℕ) (A : List Move), PrimesIn P A →
    (∀ m ∈ A, ∃ i p, m = .split i p) → shiftPos j A = j + growth A
  | _, [], _, _ => rfl
  | j, .split _ p :: A, ⟨hp, hA⟩, hs => by
    have := hpos p hp
    show shiftPos (j + p - 1) A = j + (p - 1 + growth A)
    rw [shiftPos_eq hpos (j + p - 1) A hA fun m hm => hs m (List.mem_cons_of_mem _ hm)]
    omega
  | _, .swap _ :: _, _, hs => by
    obtain ⟨i, p, h⟩ := hs _ List.mem_cons_self
    cases h

theorem split_of_locS {o : ℕ} : ∀ {h : ℕ} {A : List Move}, LocS o h A → ∀ m ∈ A, ∃ i p, m = .split i p
  | _, [], _, _, hm => absurd hm List.not_mem_nil
  | _, .split i p :: A, ⟨_, _, h3⟩, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨i, p, rfl⟩
    · exact split_of_locS h3 m hm
  | _, .swap _ :: _, h, _, _ => (show False from h).elim

section Decomp

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

/-- **Tree decomposition.** A split word on a block `[o, h)` is a word on `[o, f)` followed by a
word on the rest. -/
theorem decomp (o : ℕ) : ∀ (w : List Move) (n f h : ℕ), h ≤ n → o < f → f ≤ h → LocS o h w →
    PrimesIn P w → ∃ A B, LocS o f A ∧ LocS (f + growth A) (h + growth A) B ∧ PrimesIn P A ∧
      PrimesIn P B ∧ growth A + growth B = growth w ∧ toH P n w = toH P n (A ++ B)
  | [], _, _, _, _, _, _, _, _ => ⟨[], [], trivial, trivial, trivial, trivial, rfl, rfl⟩
  | .swap _ :: _, _, _, _, _, _, _, hw, _ => (show False from hw).elim
  | .split i p :: w, n, f, h, hn, hof, hfh, ⟨h1, h2, hw⟩, ⟨hp, hpw⟩ => by
    have hp1 := hpos p hp
    rcases Nat.lt_or_ge i f with hif | hif
    · -- the split acts on the first part
      obtain ⟨A, B, hA, hB', hpA, hpB, hg, e⟩ :=
        decomp o w (n + p - 1) (f + (p - 1)) (h + (p - 1)) (by omega) (by omega) (by omega) hw hpw
      refine ⟨.split i p :: A, B, ⟨by omega, hif, hA⟩, ?_, ⟨hp, hpA⟩, hpB, ?_, ?_⟩
      · have e1 : f + growth (Move.split i p :: A) = f + (p - 1) + growth A := by
          simp only [growth]; omega
        have e2 : h + growth (Move.split i p :: A) = h + (p - 1) + growth A := by
          simp only [growth]; omega
        rw [e1, e2]; exact hB'
      · simp only [growth]; omega
      · rw [List.cons_append, toH_cons, toH_cons, lev_split p (by omega), e]
    · -- the split acts on the rest: move it past the first part
      obtain ⟨A, B, hA, hB', hpA, hpB, hg, e⟩ :=
        decomp o w (n + p - 1) f (h + (p - 1)) (by omega) hof (by omega) hw hpw
      have hsA := split_of_locS hA
      have hL : LeftOf i A := leftOf_of_locS hpos hA hpA hif
      have hsh : shiftPos i A = i + growth A := shiftPos_eq hpos i A hpA hsA
      refine ⟨A, .split (i + growth A) p :: B, hA, ⟨by omega, by omega, ?_⟩, hpA, ⟨hp, hpB⟩, ?_, ?_⟩
      · rw [show h + growth A + (p - 1) = h + (p - 1) + growth A by omega]; exact hB'
      · simp only [growth]; omega
      · have lA : levW n A = n + growth A :=
          levW_locB hpos o A n f (by omega) (locB_of_locS hA) hpA
        have lpA : levW n (.split i p :: A) = n + p - 1 + growth A := by
          rw [levW_cons, lev_split p (by omega),
            levW_locB hpos o A (n + p - 1) f (by omega) (locB_of_locS hA) hpA]
        have hpush := push_split hB hP2 hpos hp A n i (by omega) hL hpA
        rw [hsh] at hpush
        have lpush : levW n (.split i p :: A) = levW n (A ++ [.split (i + growth A) p]) := by
          rw [lpA, levW_append, lA, levW_cons, levW_nil, lev_split p (by omega)]
          omega
        calc toH P n (.split i p :: w)
            = toH P n (.split i p :: (A ++ B)) := by
              rw [toH_cons, toH_cons, lev_split p (by omega), e]
          _ = toH P n ((.split i p :: A) ++ B) := rfl
          _ = toH P n ((A ++ [.split (i + growth A) p]) ++ B) := toH_prefix hpush lpush B
          _ = toH P n (A ++ .split (i + growth A) p :: B) := by
              rw [List.append_assoc, List.singleton_append]

end Decomp

end GroupApproximation.ClassTransposition.Presentation
