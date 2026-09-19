import GroupApproximation.ClassTransposition.Presentation.Transfer

/-!
# Words acting inside a block of boxes

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
step O1, in `H P`).

A word acting inside the block `[lo, hi)` leaves the boxes left of the block in place
(`real_get_left`) and shifts the boxes right of it by its growth (`real_get_right`). The boxes it
creates are sub-boxes of the block: their moduli are multiples of any common divisor of the block's
moduli (`real_dvd`). `Unif b lo hi M` says that every box of `b` in `[lo, hi)` has modulus `M`; swaps
inside the block do not change it (`unif_of_real_swaps`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem kids_m {E X : Box} {p : ℕ} (h : X ∈ kids E p) : X.m = p * E.m := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
  rw [place_m, child_m]

theorem splitAt_get_lt : ∀ (b : List Box) (i p j : ℕ), j < i → (splitAt b i p)[j]? = b[j]?
  | [], _, _, _, _ => rfl
  | _ :: _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, _, 0, _ => rfl
  | _ :: b, i + 1, p, j + 1, h => splitAt_get_lt b i p j (by omega)

theorem splitAt_get_ge {p : ℕ} (hp : 1 ≤ p) : ∀ (b : List Box) (i j : ℕ), i < j → i < b.length →
    (splitAt b i p)[j + (p - 1)]? = b[j]?
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | E :: b, 0, j, hj, _ => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    show (kids E p ++ b)[j + 1 + (p - 1)]? = (E :: b)[j + 1]?
    rw [List.getElem?_append_right (show (kids E p).length ≤ j + 1 + (p - 1) by
      rw [length_kids]; omega), length_kids, show j + 1 + (p - 1) - p = j by omega]
    rfl
  | E :: b, i + 1, j, hj, h => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    show (E :: splitAt b i p)[j + 1 + (p - 1)]? = (E :: b)[j + 1]?
    rw [show j + 1 + (p - 1) = (j + (p - 1)) + 1 by omega]
    exact splitAt_get_ge hp b i j (by omega) (by simpa using h)

theorem splitAt_get_mid {p : ℕ} : ∀ (b : List Box) (i c : ℕ) (E : Box), b[i]? = some E → c < p →
    (splitAt b i p)[i + c]? = (kids E p)[c]?
  | [], _, _, _, h, _ => by simp at h
  | E' :: b, 0, c, E, h, hc => by
    have hE : E' = E := by simpa using h
    rw [← hE]
    show (kids E' p ++ b)[0 + c]? = (kids E' p)[c]?
    rw [zero_add, List.getElem?_append_left (show c < (kids E' p).length by
      rw [length_kids]; exact hc)]
  | _ :: b, i + 1, c, E, h, hc => by
    show (_ :: splitAt b i p)[i + 1 + c]? = _
    rw [show i + 1 + c = (i + c) + 1 by omega]
    exact splitAt_get_mid b i c E h hc

theorem swap_s_of_ne {k j : ℕ} (h1 : j ≠ k) (h2 : j ≠ k + 1) : Coxeter.s k j = j := by
  simp only [Coxeter.s]
  exact swap_apply_of_ne_of_ne h1 h2

/-- A word acting inside `[lo, hi)` leaves the boxes left of `lo` in place. -/
theorem real_get_left (hpos : ∀ p ∈ P' P, 2 ≤ p) {lo : ℕ} : ∀ (w : List Move) (b : List Box)
    (hi : ℕ), LocB lo hi w → PrimesIn P w → hi ≤ b.length → ∀ j < lo, (real b w)[j]? = b[j]?
  | [], _, _, _, _, _, _, _ => rfl
  | .split i p :: w, b, hi, ⟨h1, h2, h3⟩, ⟨hp, hw⟩, hb, j, hj => by
    have := hpos p hp
    have hl : (splitAt b i p).length = b.length + p - 1 := length_splitAt b i p (by omega)
    show (real (splitAt b i p) w)[j]? = b[j]?
    rw [real_get_left hpos w (splitAt b i p) (hi + (p - 1)) h3 hw (by omega) j hj]
    exact splitAt_get_lt b i p j (by omega)
  | .swap k :: w, b, hi, ⟨h1, h2, h3⟩, hw, hb, j, hj => by
    show (real (swapAt b k) w)[j]? = b[j]?
    rw [real_get_left hpos w (swapAt b k) hi h3 hw (by rw [length_swapAt]; exact hb) j hj,
      getElem?_swapAt b k (by omega), swap_s_of_ne (k := k) (j := j) (by omega) (by omega)]

/-- A word acting inside `[lo, hi)` shifts the boxes right of the block by its growth. -/
theorem real_get_right (hpos : ∀ p ∈ P' P, 2 ≤ p) {lo : ℕ} : ∀ (w : List Move) (b : List Box)
    (hi : ℕ), LocB lo hi w → PrimesIn P w → hi ≤ b.length → ∀ j, hi ≤ j →
      (real b w)[j + growth w]? = b[j]?
  | [], _, _, _, _, _, _, _ => rfl
  | .split i p :: w, b, hi, ⟨h1, h2, h3⟩, ⟨hp, hw⟩, hb, j, hj => by
    have := hpos p hp
    have hl : (splitAt b i p).length = b.length + p - 1 := length_splitAt b i p (by omega)
    show (real (splitAt b i p) w)[j + (p - 1 + growth w)]? = b[j]?
    rw [← add_assoc, real_get_right hpos w (splitAt b i p) (hi + (p - 1)) h3 hw (by omega)
      (j + (p - 1)) (by omega)]
    exact splitAt_get_ge (p := p) (by omega) b i j (by omega) (by omega)
  | .swap k :: w, b, hi, ⟨h1, h2, h3⟩, hw, hb, j, hj => by
    show (real (swapAt b k) w)[j + growth w]? = b[j]?
    rw [real_get_right hpos w (swapAt b k) hi h3 hw (by rw [length_swapAt]; exact hb) j hj,
      getElem?_swapAt b k (by omega), swap_s_of_ne (k := k) (j := j) (by omega) (by omega)]

/-- The boxes a split word creates inside `[lo, hi)` have moduli divisible by any common divisor
of the block's moduli. -/
theorem real_dvd (hpos : ∀ p ∈ P' P, 2 ≤ p) {lo : ℕ} {d : ℤ} : ∀ (w : List Move) (b : List Box)
    (hi : ℕ), LocS lo hi w → PrimesIn P w → hi ≤ b.length →
    (∀ j, lo ≤ j → j < hi → ∀ F, b[j]? = some F → d ∣ F.m) →
    ∀ j, lo ≤ j → j < hi + growth w → ∀ F, (real b w)[j]? = some F → d ∣ F.m
  | [], _, _, _, _, _, h, j, h1, h2, F, hF => h j h1 (by simpa [growth] using h2) F hF
  | .swap _ :: _, _, _, hw, _, _, _, _, _, _, _, _ => (show False from hw).elim
  | .split i p :: w, b, hi, ⟨h1, h2, h3⟩, ⟨hp, hw⟩, hb, h, j, hj1, hj2, F, hF => by
    have := hpos p hp
    have hl : (splitAt b i p).length = b.length + p - 1 := length_splitAt b i p (by omega)
    have hj2' : j < hi + (p - 1) + growth w := by simp only [growth] at hj2; omega
    refine real_dvd hpos w (splitAt b i p) (hi + (p - 1)) h3 hw (by omega) ?_ j hj1 hj2' F hF
    intro j' hj1' hk2 F' hF'
    rcases Nat.lt_or_ge j' i with hlt | hge
    · rw [splitAt_get_lt b i p j' hlt] at hF'
      exact h j' hj1' (by omega) F' hF'
    · rcases Nat.lt_or_ge j' (i + p) with hlt2 | hge2
      · obtain ⟨c, rfl⟩ : ∃ c, j' = i + c := ⟨j' - i, by omega⟩
        have hib : i < b.length := by omega
        have hE : b[i]? = some b[i] := List.getElem?_eq_getElem hib
        rw [splitAt_get_mid (p := p) b i c _ hE (by omega)] at hF'
        rw [kids_m (List.mem_of_getElem? hF')]
        exact Dvd.dvd.mul_left (h i h1 h2 _ hE) _
      · obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + (p - 1) := ⟨j' - (p - 1), by omega⟩
        rw [splitAt_get_ge (p := p) (by omega) b i j'' (by omega) (by omega)] at hF'
        exact h j'' (by omega) (by omega) F' hF'

/-! ### Uniform blocks -/

/-- Every box of `b` at a position in `[lo, hi)` has modulus `M`. -/
def Unif (b : List Box) (lo hi : ℕ) (M : ℤ) : Prop :=
  ∀ j, lo ≤ j → j < hi → ∀ F, b[j]? = some F → F.m = M

theorem Unif.mono {b : List Box} {lo hi lo' hi' : ℕ} {M : ℤ} (h : Unif b lo hi M)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : Unif b lo' hi' M :=
  fun j hj1 hj2 F hF => h j (by omega) (by omega) F hF

theorem unif_swapAt_of {b : List Box} {lo hi k : ℕ} {M : ℤ} (hk1 : lo ≤ k) (hk2 : k + 1 < hi)
    (hb : hi ≤ b.length) (h : Unif b lo hi M) : Unif (swapAt b k) lo hi M := by
  intro j hj1 hj2 F hF
  rw [getElem?_swapAt b k (by omega)] at hF
  have e : lo ≤ Coxeter.s k j ∧ Coxeter.s k j < hi := by
    simp only [Coxeter.s, swap_apply_def]
    split_ifs <;> omega
  exact h _ e.1 e.2 F hF

theorem unif_of_swapAt {b : List Box} {lo hi k : ℕ} {M : ℤ} (hk1 : lo ≤ k) (hk2 : k + 1 < hi)
    (hb : hi ≤ b.length) (h : Unif (swapAt b k) lo hi M) : Unif b lo hi M := by
  have := unif_swapAt_of hk1 hk2 (by rw [length_swapAt]; exact hb) h
  rwa [swapAt_swapAt] at this

theorem unif_of_mapSwap {lo hi : ℕ} {M : ℤ} : ∀ (σ : List ℕ) (b : List Box),
    (∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi) → hi ≤ b.length → Unif (real b (σ.map Move.swap)) lo hi M →
      Unif b lo hi M
  | [], _, _, _, h => h
  | k :: σ, b, hσ, hb, h => by
    have hk := hσ k List.mem_cons_self
    have h' := unif_of_mapSwap σ (swapAt b k) (fun k' hk' => hσ k' (List.mem_cons_of_mem _ hk'))
      (by rw [length_swapAt]; exact hb) h
    exact unif_of_swapAt hk.1 hk.2 hb h'

theorem unif_of_real_swaps {lo hi : ℕ} {M : ℤ} (σ : List ℕ) (b : List Box)
    (hσ : ∀ k ∈ σ, lo ≤ k ∧ k + 1 < hi) (hb : hi ≤ b.length)
    (h : Unif (real b (swaps 0 σ)) lo hi M) : Unif b lo hi M := by
  rw [swaps_zero] at h
  exact unif_of_mapSwap σ b hσ hb h

end GroupApproximation.ClassTransposition.Presentation
