import GroupApproximation.CharClass.CupOneSign
import GroupApproximation.CharClass.SteenrodCupEdge

/-!
# The signed cancellation

`SteenrodCutCancel.cut_insert_cancel` is the whole mathematical content of Steenrod's
coboundary formula, stated for an abelian group of exponent two: summing over the
vertices that are not yet cut points the two ways of turning one into a cut point and
deleting it again leaves the two orders of the original cut, because `Ξ t + Ξ (t+1)`
telescopes.

Over a ring in which `1 ≠ -1` the same sum telescopes with a **sign**: the two terms
attached to `c` are `Ξ (c+1) - Ξ c` for the weighted

```text
Ξ t = telTerm Θ s t = (-1) ^ telExp s t * Θ (cutLow {s} t) (cutHigh {s} t).
```

Two things replace `x + x = 0`.  The term at the *old* cut point drops because the
threshold does not move there (`cutLow_succ_of_mem`) **and** the two weights agree
(`telExp_succ_self`); and the sum telescopes to `Ξ N - Ξ 0` rather than `Ξ N + Ξ 0`.

Only one-point cuts are needed (`cutIndex 1`), which is what the cup-1 coboundary
formula's leftover produces, so the cut is a vertex rather than a set.
-/

namespace GroupApproximation
namespace CharClass

/-! ## 1. Parity of a product

`cutExp` is the only place a product of two non-constant naturals occurs, and these
three lemmas evaluate it modulo two.  Everything after them is linear arithmetic. -/

theorem mul_self_mod_two (x : ℕ) : (x * x) % 2 = x % 2 := by
  rcases Nat.even_or_odd x with h | h
  · obtain ⟨m, rfl⟩ := h
    have hx : (m + m) * (m + m) = 2 * (2 * (m * m)) := by ring
    omega
  · obtain ⟨m, rfl⟩ := h
    have hx : (2 * m + 1) * (2 * m + 1) = 2 * (2 * (m * m) + m + m) + 1 := by ring
    omega

theorem pair_prod_mod_two (x M : ℕ) : ((x + M) * (x + 1)) % 2 = (M * x + M) % 2 := by
  have hexp : (x + M) * (x + 1) = x * x + x + M * x + M := by ring
  rw [hexp]
  have hsq := mul_self_mod_two x
  omega

/-- **The exponent of a two-point cut, modulo two.** -/
theorem cutExp_pair_mod_two {N : ℕ} {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    cutExp ({t₀, t₁} : Finset (Fin N)) % 2
      = (N * (t₀.val + t₁.val) + N + t₀.val * t₁.val) % 2 := by
  have hlt : t₀.val < t₁.val := h
  have h1 : t₁.val < N := t₁.isLt
  rw [cutExp_pair h]
  have hu : (t₀.val + 1 + (N - t₁.val) + 1) % 2 = (t₀.val + t₁.val + N) % 2 := by omega
  have hv : (t₁.val + 1 - t₀.val) % 2 = (t₀.val + t₁.val + 1) % 2 := by omega
  have hprod : ((t₀.val + 1 + (N - t₁.val) + 1) * (t₁.val + 1 - t₀.val)) % 2
      = ((t₀.val + t₁.val + N) * (t₀.val + t₁.val + 1)) % 2 := by
    rw [Nat.mul_mod, hu, hv, ← Nat.mul_mod]
  have hpp := pair_prod_mod_two (t₀.val + t₁.val) N
  omega

/-! ## 2. The telescope weight -/

/-- **The weight of a threshold.**  The two branches meet at `t = s`, which is what
makes the term at the old cut point drop. -/
def telExp {N : ℕ} (s : Fin N) (t : ℕ) : ℕ :=
  N * (t + s.val) + t * s.val + 1 + (if t ≤ s.val then N + t else 0)

theorem telExp_of_le {N : ℕ} (s : Fin N) {t : ℕ} (h : t ≤ s.val) :
    telExp s t = N * (t + s.val) + t * s.val + 1 + (N + t) := by
  unfold telExp
  rw [if_pos h]

theorem telExp_of_gt {N : ℕ} (s : Fin N) {t : ℕ} (h : ¬ t ≤ s.val) :
    telExp s t = N * (t + s.val) + t * s.val + 1 := by
  unfold telExp
  rw [if_neg h]

/-- The two branches agree at the cut point: this is what replaces `x + x = 0`. -/
theorem telExp_succ_self {N : ℕ} (s : Fin N) :
    telExp s (s.val + 1) % 2 = telExp s s.val % 2 := by
  rw [telExp_of_le s (le_refl s.val), telExp_of_gt s (by omega)]
  have h1 : N * (s.val + 1 + s.val) = N * (s.val + s.val) + N := by ring
  have h2 : (s.val + 1) * s.val = s.val * s.val + s.val := by ring
  have h3 : N * (s.val + s.val) = 2 * (N * s.val) := by ring
  have hsq := mul_self_mod_two s.val
  omega

theorem telExp_top {N : ℕ} (s : Fin N) : telExp s N % 2 = (N + 1) % 2 := by
  have hs : s.val < N := s.isLt
  rw [telExp_of_gt s (by omega)]
  have h1 : N * (N + s.val) = N * N + N * s.val := by ring
  have hsq := mul_self_mod_two N
  omega

theorem telExp_bot {N : ℕ} (s : Fin N) : telExp s 0 % 2 = (N + N * s.val + 1) % 2 := by
  rw [telExp_of_le s (Nat.zero_le _)]
  have h1 : N * (0 + s.val) = N * s.val := by ring
  omega

/-- The term of the telescope at threshold `t`. -/
def telTerm {K : Type} [CommRing K] {N : ℕ} (Θ : Finset (Fin N) → Finset (Fin N) → K)
    (s : Fin N) (t : ℕ) : K :=
  (-1 : K) ^ telExp s t
    * Θ (cutLow ({s} : Finset (Fin N)) t) (cutHigh ({s} : Finset (Fin N)) t)

/-! ## 3. The signed cancellation -/

/-- **The signed cancellation.**  For a one-point cut `{s}`, summing over every other
vertex the two ways of turning it into a second cut point and deleting it again
telescopes to the two orders of `{s}` itself, with the signs the cup-1 coboundary
formula supplies. -/
theorem cut_insert_cancel_signed {K : Type} [CommRing K] {N : ℕ}
    (Θ : Finset (Fin N) → Finset (Fin N) → K) (s : Fin N) :
    ∑ c ∈ (({s} : Finset (Fin N))ᶜ),
        ((-1 : K) ^ (cutExp (insert c ({s} : Finset (Fin N)))
              + cutRank (cutU (insert c ({s} : Finset (Fin N)))) c)
            * Θ ((cutU (insert c ({s} : Finset (Fin N)))).erase c)
                (cutV (insert c ({s} : Finset (Fin N))))
          + (-1 : K) ^ ((cutU (insert c ({s} : Finset (Fin N)))).card - 1
              + cutExp (insert c ({s} : Finset (Fin N)))
              + cutRank (cutV (insert c ({s} : Finset (Fin N)))) c)
            * Θ (cutU (insert c ({s} : Finset (Fin N))))
                ((cutV (insert c ({s} : Finset (Fin N)))).erase c))
      = (-1 : K) ^ (N + 1) * Θ (cutU ({s} : Finset (Fin N))) (cutV ({s} : Finset (Fin N)))
        - (-1 : K) ^ (N + N * s.val + 1)
            * Θ (cutV ({s} : Finset (Fin N))) (cutU ({s} : Finset (Fin N))) := by
  classical
  have key : ∀ c ∈ (({s} : Finset (Fin N))ᶜ),
      ((-1 : K) ^ (cutExp (insert c ({s} : Finset (Fin N)))
            + cutRank (cutU (insert c ({s} : Finset (Fin N)))) c)
          * Θ ((cutU (insert c ({s} : Finset (Fin N)))).erase c)
              (cutV (insert c ({s} : Finset (Fin N))))
        + (-1 : K) ^ ((cutU (insert c ({s} : Finset (Fin N)))).card - 1
            + cutExp (insert c ({s} : Finset (Fin N)))
            + cutRank (cutV (insert c ({s} : Finset (Fin N)))) c)
          * Θ (cutU (insert c ({s} : Finset (Fin N))))
              ((cutV (insert c ({s} : Finset (Fin N)))).erase c))
      = telTerm Θ s (c.val + 1) - telTerm Θ s c.val := by
    intro c hc'
    have hc : c ∉ ({s} : Finset (Fin N)) := Finset.mem_compl.1 hc'
    have hcs : c ≠ s := by
      intro hcc
      exact hc (by rw [hcc]; exact Finset.mem_singleton_self s)
    have hsN : s.val < N := s.isLt
    have hcN : c.val < N := c.isLt
    by_cases hcU : c ∈ cutU ({s} : Finset (Fin N))
    · -- the new cut point is below the old one
      have hle : c ≤ s := by
        rw [cutU_singleton] at hcU
        exact Finset.mem_Iic.1 hcU
      have hlt : c < s := lt_of_le_of_ne hle hcs
      have hltv : c.val < s.val := hlt
      have hrankV : cutRank (cutV ({c, s} : Finset (Fin N))) c = 0 := by
        rw [cutRank_cutV_pair hlt c, if_pos (show c.val ≤ s.val by omega)]
        omega
      have hrankU : cutRank (cutU ({c, s} : Finset (Fin N))) c = c.val := by
        have hsum := cutRank_cutU_add_cutRank_cutV ({c, s} : Finset (Fin N)) c
        rw [cutRank_pair (ne_of_lt hlt) c, hrankV, if_neg (lt_irrefl c),
          if_neg (lt_asymm hlt)] at hsum
        omega
      have hcard : (cutU ({c, s} : Finset (Fin N))).card = c.val + 1 + (N - s.val) :=
        card_cutU_pair hlt
      have hexp := cutExp_pair_mod_two hlt
      have hs1 : (-1 : K) ^ (cutExp ({c, s} : Finset (Fin N))
            + cutRank (cutU ({c, s} : Finset (Fin N))) c)
          = - (-1 : K) ^ telExp s c.val := by
        have hpar : (cutExp ({c, s} : Finset (Fin N))
              + cutRank (cutU ({c, s} : Finset (Fin N))) c) % 2
            = (telExp s c.val + 1) % 2 := by
          rw [hrankU, telExp_of_le s (le_of_lt hltv)]
          omega
        rw [neg_one_pow_congr_mod_two (K := K) hpar, pow_succ]
        ring
      have hs2 : (-1 : K) ^ ((cutU ({c, s} : Finset (Fin N))).card - 1
            + cutExp ({c, s} : Finset (Fin N))
            + cutRank (cutV ({c, s} : Finset (Fin N))) c)
          = (-1 : K) ^ telExp s (c.val + 1) := by
        have hpar : ((cutU ({c, s} : Finset (Fin N))).card - 1
              + cutExp ({c, s} : Finset (Fin N))
              + cutRank (cutV ({c, s} : Finset (Fin N))) c) % 2
            = telExp s (c.val + 1) % 2 := by
          rw [hrankV, hcard, telExp_of_le s (by omega)]
          have h1 : N * (c.val + 1 + s.val) = N * (c.val + s.val) + N := by ring
          have h2 : (c.val + 1) * s.val = c.val * s.val + s.val := by ring
          omega
        exact neg_one_pow_congr_mod_two (K := K) hpar
      -- the two `.erase` rewrites must come first: rewriting the bare `cutV (insert c S)`
      -- would consume the occurrence inside `(cutV (insert c S)).erase c`.
      rw [hs1, hs2, cutU_insert_erase_eq_cutLow hc hcU,
        cutV_insert_erase_eq_cutHigh_succ hc hcU, cutU_insert_eq_cutLow_succ hc hcU,
        cutV_insert_eq_cutHigh hc hcU]
      unfold telTerm
      ring
    · -- the new cut point is above the old one
      have hlt : s < c := by
        rcases lt_trichotomy s c with hh | hh | hh
        · exact hh
        · exact absurd hh.symm hcs
        · refine absurd ?_ hcU
          rw [cutU_singleton]
          exact Finset.mem_Iic.2 (le_of_lt hh)
      have hltv : s.val < c.val := hlt
      have hins : insert c ({s} : Finset (Fin N)) = ({s, c} : Finset (Fin N)) :=
        Finset.pair_comm c s
      have hrankV : cutRank (cutV ({s, c} : Finset (Fin N))) c = c.val - s.val := by
        rw [cutRank_cutV_pair hlt c, if_pos (le_refl c.val)]
      have hrankU : cutRank (cutU ({s, c} : Finset (Fin N))) c = s.val + 1 := by
        have hsum := cutRank_cutU_add_cutRank_cutV ({s, c} : Finset (Fin N)) c
        rw [cutRank_pair (ne_of_lt hlt) c, hrankV, if_pos hlt, if_neg (lt_irrefl c)] at hsum
        omega
      have hcard : (cutU ({s, c} : Finset (Fin N))).card = s.val + 1 + (N - c.val) :=
        card_cutU_pair hlt
      have hexp := cutExp_pair_mod_two hlt
      -- The four `insert` lemmas below are stated for `insert c S`, so `hins` is used
      -- only inside the sign computations and never on the goal.
      have hs1 : (-1 : K) ^ (cutExp (insert c ({s} : Finset (Fin N)))
            + cutRank (cutU (insert c ({s} : Finset (Fin N)))) c)
          = (-1 : K) ^ telExp s (c.val + 1) := by
        rw [hins]
        have hpar : (cutExp ({s, c} : Finset (Fin N))
              + cutRank (cutU ({s, c} : Finset (Fin N))) c) % 2
            = telExp s (c.val + 1) % 2 := by
          rw [hrankU, telExp_of_gt s (by omega)]
          have h1 : N * (c.val + 1 + s.val) = N * (s.val + c.val) + N := by ring
          have h2 : (c.val + 1) * s.val = s.val * c.val + s.val := by ring
          omega
        exact neg_one_pow_congr_mod_two (K := K) hpar
      have hs2 : (-1 : K) ^ ((cutU (insert c ({s} : Finset (Fin N)))).card - 1
            + cutExp (insert c ({s} : Finset (Fin N)))
            + cutRank (cutV (insert c ({s} : Finset (Fin N)))) c)
          = - (-1 : K) ^ telExp s c.val := by
        rw [hins]
        have hpar : ((cutU ({s, c} : Finset (Fin N))).card - 1
              + cutExp ({s, c} : Finset (Fin N))
              + cutRank (cutV ({s, c} : Finset (Fin N))) c) % 2
            = (telExp s c.val + 1) % 2 := by
          rw [hrankV, hcard, telExp_of_gt s (by omega)]
          have h1 : N * (c.val + s.val) = N * (s.val + c.val) := by ring
          have h2 : c.val * s.val = s.val * c.val := by ring
          omega
        rw [neg_one_pow_congr_mod_two (K := K) hpar, pow_succ]
        ring
      rw [hs1, hs2, cutU_insert_erase_eq_cutLow_succ hc hcU,
        cutV_insert_erase_eq_cutHigh hc hcU, cutU_insert_eq_cutLow hc hcU,
        cutV_insert_eq_cutHigh_succ hc hcU]
      unfold telTerm
      ring
  have hzero : ∀ c ∈ ({s} : Finset (Fin N)),
      telTerm Θ s (c.val + 1) - telTerm Θ s c.val = 0 := by
    intro c hc
    rw [Finset.mem_singleton.1 hc]
    unfold telTerm
    rw [cutLow_succ_of_mem (Finset.mem_singleton_self s),
      cutHigh_succ_of_mem (Finset.mem_singleton_self s),
      neg_one_pow_congr_mod_two (K := K) (telExp_succ_self s)]
    ring
  calc ∑ c ∈ (({s} : Finset (Fin N))ᶜ),
        ((-1 : K) ^ (cutExp (insert c ({s} : Finset (Fin N)))
              + cutRank (cutU (insert c ({s} : Finset (Fin N)))) c)
            * Θ ((cutU (insert c ({s} : Finset (Fin N)))).erase c)
                (cutV (insert c ({s} : Finset (Fin N))))
          + (-1 : K) ^ ((cutU (insert c ({s} : Finset (Fin N)))).card - 1
              + cutExp (insert c ({s} : Finset (Fin N)))
              + cutRank (cutV (insert c ({s} : Finset (Fin N)))) c)
            * Θ (cutU (insert c ({s} : Finset (Fin N))))
                ((cutV (insert c ({s} : Finset (Fin N)))).erase c))
      = ∑ c ∈ (({s} : Finset (Fin N))ᶜ),
          (telTerm Θ s (c.val + 1) - telTerm Θ s c.val) := Finset.sum_congr rfl key
    _ = ∑ c : Fin N, (telTerm Θ s (c.val + 1) - telTerm Θ s c.val) := by
        rw [← Finset.sum_add_sum_compl ({s} : Finset (Fin N))
          (fun c : Fin N => telTerm Θ s (c.val + 1) - telTerm Θ s c.val),
          Finset.sum_eq_zero hzero, zero_add]
    _ = ∑ j ∈ Finset.range N, (telTerm Θ s (j + 1) - telTerm Θ s j) :=
        Fin.sum_univ_eq_sum_range (fun j => telTerm Θ s (j + 1) - telTerm Θ s j) N
    _ = telTerm Θ s N - telTerm Θ s 0 := Finset.sum_range_sub (telTerm Θ s) N
    _ = (-1 : K) ^ (N + 1) * Θ (cutU ({s} : Finset (Fin N))) (cutV ({s} : Finset (Fin N)))
          - (-1 : K) ^ (N + N * s.val + 1)
              * Θ (cutV ({s} : Finset (Fin N))) (cutU ({s} : Finset (Fin N))) := by
        unfold telTerm
        rw [cutLow_top, cutHigh_top, cutLow_zero, cutHigh_zero,
          neg_one_pow_congr_mod_two (K := K) (telExp_top s),
          neg_one_pow_congr_mod_two (K := K) (telExp_bot s)]

end CharClass
end GroupApproximation
