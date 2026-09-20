import GroupApproximation.ClassTransposition.Presentation.RangeLe

/-!
# Odd splits evaluate into `CT_P(ℤ)`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1; the
input `piecewise-canonical-permutations-are-transposition-products`, Lemma 7).

Modulo the normal subgroup `NH`, for an odd `p ∈ P`:
* relation (d) at the tail: `X_p(j+1) ≡ Y_p(j+2)`;
* relation (c) with `q = 2` at the tail: `Y_p(j+1) ≡ X_p(j+1) · Y_p(j+p+1)`;
* the shift: `Y_p(m+1) ≡ Y_p(m)` for `m ≥ 2`.
So `Y_p(2) ≡ Y_p(2)²`, hence every `X_p` and `Y_p` lies in `NH` (`odd_mem_nh`), and so does every
generator (`range_le`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

section Y

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
  (hprime : ∀ p ∈ P' P, p.Prime)
include hB hP2 hpos hprime

theorem odd_mem_nh {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    gH (tY p hp) (m + 1) ∈ NH hpos hP2 ∧ gH (tX p (mem_P'_of_mem hp)) (m + 1) ∈ NH hpos hP2 := by
  haveI := nh_normal hB hP2 hpos hprime
  have h0 : ∀ x ∈ NH hpos hP2, (QuotientGroup.mk' (NH hpos hP2) x) = 1 :=
    fun x hx => (QuotientGroup.eq_one_iff x).2 hx
  set φ := QuotientGroup.mk' (NH hpos hP2)
  have hp' : p ∈ P' P := mem_P'_of_mem hp
  have hp2 : p ≠ 2 := ne_two_of_mem hP2 hp
  have hp1 := hpos p hp'
  -- (d) at the tail
  have hd : ∀ j, φ (gH (tX p hp') (j + 1)) = φ (gH (tY p hp) (j + 2)) := by
    intro j
    have e := dk1_all hB hp' (j + 2) j (by omega)
    have L : toH P (j + 2) [.swap j, .split (j + 1) p] =
        hatH P (.swap j) (j + 2) * gH (tY p hp) (j + 2) := by
      rw [toH_cons, lev_swap, toH_single, hatH_split_tail (show j + 1 + 1 = j + 2 by omega) hp hp2]
    have R : toH P (j + 2) (.split j p :: swaps j (List.range p).reverse) =
        gH (tX p hp') (j + 1) * toH P (j + 2 + p - 1) (swaps j (List.range p).reverse) := by
      rw [toH_cons, hatH_split_front (show j + 1 < j + 2 by omega) hp',
        lev_split p (show j < j + 2 by omega)]
    rw [L, R] at e
    have e' := congrArg φ e
    rw [map_mul, map_mul, h0 _ (swap_mem_nh hP2 hpos hprime _ _),
      h0 _ (swaps_mem_nh hP2 hpos hprime _ _ _), one_mul, mul_one] at e'
    exact e'.symm
  -- (c) with `q = 2` at the tail
  have hc : ∀ j, φ (gH (tY p hp) (j + 1)) =
      φ (gH (tX p hp') (j + 1)) * φ (gH (tY p hp) (j + p + 1)) := by
    intro j
    have e := cx_all hB hp' (two_mem P) hp2 (by omega) (by omega) (j + 1) j (by omega)
    have L : toH P (j + 1) (.split j p :: layer j p 2) =
        gH (tY p hp) (j + 1) * toH P (j + 1 + p - 1) (layer j p 2) := by
      rw [toH_cons, hatH_split_tail (show j + 1 = j + 1 from rfl) hp hp2,
        lev_split p (show j < j + 1 by omega)]
    have R : toH P (j + 1) (.split j 2 :: layer j 2 p ++ swaps j (crtWord p 2)) =
        gH (tX p hp') (j + 1) * gH (tY p hp) (j + p + 1) *
          toH P (levW (j + 1) (.split j 2 :: layer j 2 p)) (swaps j (crtWord p 2)) := by
      rw [toH_append, layer_two, toH_cons, hatH_split_tail_two (show j + 1 = j + 1 from rfl),
        one_mul, lev_split 2 (show j < j + 1 by omega), toH_cons, toH_single,
        hatH_split_front (show j + 1 < j + 1 + 2 - 1 by omega) hp',
        lev_split p (show j < j + 1 + 2 - 1 by omega),
        hatH_split_tail (show j + p + 1 = j + 1 + 2 - 1 + p - 1 by omega) hp hp2]
    rw [L, R] at e
    have hl2 : toH P (j + 1 + p - 1) (layer j p 2) ∈ NH hpos hP2 :=
      cheap_mem_nh hB hP2 hpos hprime (layer j p 2) _ fun m hm => Or.inr (by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm; exact ⟨_, rfl⟩)
    have e' := congrArg φ e
    rw [map_mul, map_mul, map_mul, h0 _ (swaps_mem_nh hP2 hpos hprime _ _ _), h0 _ hl2,
      mul_one, mul_one] at e'
    exact e'
  -- the shift
  have hs : φ (sH P) = 1 := h0 _ (two_mem_nh hB hP2 hpos hprime 0 (two_mem P))
  have hconst : ∀ m, φ (gH (tY p hp) (m + 2)) = φ (gH (tY p hp) 2) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show m + 1 + 2 = m + 2 + 1 by omega, gH_succ _ (show 2 ≤ m + 2 by omega), map_mul,
        map_mul, map_inv, hs, inv_one, one_mul, mul_one, ih]
  have hy2 : φ (gH (tY p hp) 2) = 1 := by
    have h1 := hc 1
    rw [hd 1, hconst 1, show 1 + p + 1 = (p - 1) + 2 by omega, hconst (p - 1),
      show (1 : ℕ) + 1 = 2 from rfl] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  have hy : ∀ m, φ (gH (tY p hp) (m + 1)) = 1 := by
    intro m
    rcases m with _ | m
    · rw [hc 0, hd 0, hconst 0, hy2, one_mul, show 0 + p + 1 = (p - 1) + 2 by omega,
        hconst (p - 1), hy2]
    · rw [show m + 1 + 1 = m + 2 by omega, hconst m, hy2]
  have hX : φ (gH (tX p hp') (m + 1)) = 1 := by
    rw [hd m, show m + 2 = (m + 1) + 1 by omega, hy (m + 1)]
  exact ⟨(QuotientGroup.eq_one_iff _).1 (hy m), (QuotientGroup.eq_one_iff _).1 hX⟩

/-- Every generator at a position `≥ 1` evaluates into `CT_P(ℤ)`. -/
theorem gen_mem_nh (t : Ty P) (j : ℕ) : gH t (j + 1) ∈ NH hpos hP2 := by
  rcases t with ⟨p, hp⟩ | ⟨p, hp⟩ | b
  · by_cases h2 : p = 2
    · subst h2; exact two_mem_nh hB hP2 hpos hprime j hp
    · have hpP : p ∈ P := by
        rcases hp with h | h
        · exact absurd h h2
        · exact h
      exact (odd_mem_nh hB hP2 hpos hprime hpP j).2
  · exact (odd_mem_nh hB hP2 hpos hprime hp j).1
  · cases b
    · show gH tPi (j + 1) ∈ NH hpos hP2
      rw [← hatH_swap_front (show j + 2 < j + 3 by omega)]
      exact swap_mem_nh hP2 hpos hprime j (j + 3)
    · show gH tRho (j + 1) ∈ NH hpos hP2
      rw [← hatH_swap_tail (show j + 2 = j + 2 from rfl)]
      exact swap_mem_nh hP2 hpos hprime j (j + 2)

/-- **The image of `evalH` lies in `CT_P(ℤ)`.** -/
theorem range_le : (evalH hpos hP2).range ≤ classTranspositionGroupOver P := by
  intro y hy
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hy
  refine PresentedGroup.generated_by (rels P) (NH hpos hP2) (fun x => ?_) h
  obtain ⟨t, b⟩ := x
  cases b
  · exact gen_mem_nh hB hP2 hpos hprime t 0
  · exact gen_mem_nh hB hP2 hpos hprime t 1

end Y

end GroupApproximation.ClassTransposition.Presentation
