import GroupApproximation.ClassTransposition.Presentation.Key

/-!
# The evaluation `evalH` is injective

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
steps O2–O4, in `H P`).

Every element of `H P` is a fraction `toH P 1 a * (toH P 1 a')⁻¹` of two valid words from `[ℤ]`
of the same final level: the generators are (the comb path `tp` is `1` in `H P`), and the
fractions form a subgroup by the Ore condition (`ore`) and `key`. If a fraction evaluates to `1`,
its two words have the same realization (`frac_inj`), so it is `1` by `key`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The comb path from level `1` to level `k + 1`: split the tail by `2`, `k` times. -/
def tp : ℕ → List Move
  | 0 => []
  | k + 1 => tp k ++ [.split k 2]

theorem levW_tp : ∀ k, levW 1 (tp k) = k + 1
  | 0 => rfl
  | k + 1 => by
    rw [tp, levW_append, levW_tp k, levW_cons, levW_nil, lev_split 2 (show k < k + 1 by omega)]
      <;> omega

theorem toH_tp : ∀ k, toH P 1 (tp k) = 1
  | 0 => toH_nil 1
  | k + 1 => by
    rw [tp, toH_append, toH_tp k, levW_tp k, one_mul, toH_single, hatH_split_tail_two rfl]

theorem valW_tp : ∀ k, ValW P 1 (tp k)
  | 0 => trivial
  | k + 1 => (valW_append P 1 _ _).2 ⟨valW_tp k, by
      rw [levW_tp k]; exact ⟨⟨show k < k + 1 by omega, two_mem P⟩, trivial⟩⟩

/-- The fractions of two valid words from `[ℤ]` with the same final level. -/
def FracSet (P : Set ℕ) : Set (H P) :=
  {h | ∃ a a' : List Move, ValW P 1 a ∧ ValW P 1 a' ∧ levW 1 a = levW 1 a' ∧
    h = toH P 1 a * (toH P 1 a')⁻¹}

theorem fracSet_one : (1 : H P) ∈ FracSet P :=
  ⟨[], [], trivial, trivial, rfl, by rw [toH_nil, inv_one, mul_one]⟩

theorem fracSet_inv {x : H P} (hx : x ∈ FracSet P) : x⁻¹ ∈ FracSet P := by
  obtain ⟨a, a', ha, ha', hl, rfl⟩ := hx
  exact ⟨a', a, ha', ha, hl.symm, by rw [mul_inv_rev, inv_inv]⟩

theorem mem_fracSet_single (hpos : ∀ p ∈ P' P, 2 ≤ p) {m : Move} {k : ℕ} (hm : m.Val P (k + 1)) :
    toH P (k + 1) [m] ∈ FracSet P := by
  have hge := lev_ge (hm.ok hpos) (k + 1)
  obtain ⟨j, hj⟩ : ∃ j, m.lev (k + 1) = j + 1 := ⟨m.lev (k + 1) - 1, by omega⟩
  refine ⟨tp k ++ [m], tp j, (valW_append P 1 _ _).2 ⟨valW_tp k, by
    rw [levW_tp k]; exact ⟨hm, trivial⟩⟩, valW_tp j, ?_, ?_⟩
  · rw [levW_append, levW_tp k, levW_cons, levW_nil, hj, levW_tp j]
  · rw [toH_tp j, inv_one, mul_one, toH_append, toH_tp k, levW_tp k, one_mul]

/-- Every generator at a position `≥ 1` is a fraction. -/
theorem gH_mem (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) (t : Ty P) (i : ℕ) :
    gH t (i + 1) ∈ FracSet P := by
  rcases t with ⟨p, hp⟩ | ⟨p, hp⟩ | b
  · show gH (tX p hp) (i + 1) ∈ FracSet P
    rw [← hatH_split_front (show i + 1 < i + 2 by omega) hp, ← toH_single]
    exact mem_fracSet_single hpos (k := i + 1) ⟨by omega, hp⟩
  · show gH (tY p hp) (i + 1) ∈ FracSet P
    rw [← hatH_split_tail (show i + 1 = i + 1 from rfl) hp (ne_two_of_mem hP2 hp), ← toH_single]
    exact mem_fracSet_single hpos (k := i) ⟨by omega, mem_P'_of_mem hp⟩
  · cases b
    · show gH tPi (i + 1) ∈ FracSet P
      rw [← hatH_swap_front (show i + 2 < i + 3 by omega), ← toH_single]
      exact mem_fracSet_single hpos (k := i + 2) (show i + 1 < i + 3 by omega)
    · show gH tRho (i + 1) ∈ FracSet P
      rw [← hatH_swap_tail (show i + 2 = i + 2 from rfl), ← toH_single]
      exact mem_fracSet_single hpos (k := i + 1) (show i + 1 < i + 2 by omega)

section Inj

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
  (hprime : ∀ p ∈ P' P, p.Prime)
include hB hP2 hpos hprime

theorem fracSet_mul {x y : H P} (hx : x ∈ FracSet P) (hy : y ∈ FracSet P) :
    x * y ∈ FracSet P := by
  obtain ⟨a, a', ha, ha', hl, rfl⟩ := hx
  obtain ⟨b, b', hb, hb', hl', rfl⟩ := hy
  obtain ⟨c, c', hc, hc', hr⟩ := ore hpos ha' hb
  have hk := key hB hP2 hpos hprime ((valW_append P 1 a' c).2 ⟨ha', hc⟩)
    ((valW_append P 1 b c').2 ⟨hb, hc'⟩) hr
  rw [toH_append, toH_append] at hk
  have hlr : levW 1 (a' ++ c) = levW 1 (b ++ c') := by
    have := congrArg List.length hr
    rwa [length_real, length_real, length_comb] at this
  refine ⟨a ++ c, b' ++ c', (valW_append P 1 a c).2 ⟨ha, by rw [hl]; exact hc⟩,
    (valW_append P 1 b' c').2 ⟨hb', by rw [← hl']; exact hc'⟩, ?_, ?_⟩
  · rw [levW_append, levW_append, hl, ← hl']
    rw [levW_append, levW_append] at hlr
    exact hlr
  · rw [toH_append, toH_append, hl, ← hl']
    have e : toH P 1 b = toH P 1 a' * toH P (levW 1 a') c * (toH P (levW 1 b) c')⁻¹ := by
      rw [hk]; group
    rw [e]
    group

/-- Every element of `H P` is a fraction. -/
theorem mem_fracSet (h : H P) : h ∈ FracSet P := by
  let S : Subgroup (H P) :=
    { carrier := FracSet P
      mul_mem' := fun hx hy => fracSet_mul hB hP2 hpos hprime hx hy
      one_mem' := fracSet_one
      inv_mem' := fun hx => fracSet_inv hx }
  refine PresentedGroup.generated_by (rels P) S (fun x => ?_) h
  obtain ⟨t, b⟩ := x
  cases b
  · exact gH_mem hpos hP2 t 0
  · exact gH_mem hpos hP2 t 1

/-- **Injectivity** of the evaluation. -/
theorem evalH_injective : Function.Injective (evalH hpos hP2) := by
  refine (injective_iff_map_eq_one _).2 fun h hh => ?_
  obtain ⟨a, a', ha, ha', hl, rfl⟩ := mem_fracSet hB hP2 hpos hprime h
  rw [map_mul, map_inv, mul_inv_eq_one, evalH_toH hpos hP2 one_pos ha,
    evalH_toH hpos hP2 one_pos ha', hl] at hh
  have h1 := levW_ge 1 a' (ValW.ok hpos ha')
  have hr := frac_inj (isPart_comb _ (by omega)) (isPart_real (isPart_comb 1 one_pos) a (ValW.ok hpos ha))
    (isPart_real (isPart_comb 1 one_pos) a' (ValW.ok hpos ha'))
    (by rw [length_comb, length_real, length_comb, hl]) (by rw [length_comb, length_real, length_comb])
    hh
  rw [key hB hP2 hpos hprime ha ha' hr, mul_inv_cancel]

end Inj

end GroupApproximation.ClassTransposition.Presentation
