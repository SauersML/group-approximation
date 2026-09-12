import GroupApproximation.GGT.DGOIsolatedComponentRotate

/-!
# Turning a polygon round: the cut function

`DGOIsolatedComponentRotate` rotates a closed word at a corner and carries the
distinguished component and its isolation across.  This module carries the
*polygon* across: the cut function, the endpoints, monotonicity, and the
quasi-geodesic clause, with the distinguished side arriving at index `0`.

The rotated cut function is the old one read cyclically from the corner `t`:

    d s = if s ≤ N - t then c (t + s) - c t
          else c (s - (N - t)) + (w.length - c t) ,

so side `s` of the rotated polygon is side `t + s` of the old one for
`s < N - t`, and side `s - (N - t)` for `s ≥ N - t`.  Side `0` is the old side
`t` — the distinguished one — which is why the exemption travels: the clause is
asked of `s ≠ 0` after, exactly as it was asked of `s ≠ t` before.

Concept grep before writing: `cut function`, `rotate`, `Monotone c` across the
DGO files.  `DGOIsolatedComponentRecut` and `…Straddle` refine a cut function on
a fixed word; `DGOIsolatedComponentCollapseCut` transports one along the
collapse; nothing transports one along a rotation.

## Why no side straddles the seam

The seam is at rotated index `w.length - c t`, and it is a *corner*:
`d (N - t) = c N - c t = w.length - c t`, which is also what the second branch
gives there, `c 0 = 0`.  So every side lies entirely on one side of it, and the
clause splits into two cases, each quoting the old clause with indices shifted by
`+ c t` or by `- (w.length - c t)`.  The vertex identifications are
`vertex_rotWord_le` and `vertex_rotWord_add`, and the second is where closedness
is used: past the seam the rotated path is reading `w` from its basepoint again.

## A note on the arithmetic

Every index is normalised before `omega` sees it — `t + (s+1)` to `t + s + 1`,
`s + 1 - (N-t)` to `s - (N-t) + 1` — because `c` is an uninterpreted function
there, so `c (t + (s+1))` and `c (t + s + 1)` are two atoms and omega will not
identify them.  The same discipline as the `ite` rewriting: omega is given only
goals it can actually see.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The rotated cut function -/

/-- **The polygon survives being turned round at a corner, with the
distinguished side arriving first.**

The clause is asked of `s ≠ t` in the hypothesis and delivered for `s ≠ 0`: the
old side `t` becomes the new side `0`.  `d 1 = c (t+1) - c t` records that the
new first side is the old side `t`, so a component occupying it keeps its length,
and `isComp_rotWord` keeps it a component. -/
theorem exists_rot_cut (D : RelGenSet G Λ) (mu b : ℝ) {N t : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hclosed : RelLetter.listVal w = 1) (hc0 : c 0 = 0) (hcN : c N = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1)) (ht : t < N)
    (hcqg : ∀ s : ℕ, s < N → s ≠ t → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) :
    ∃ d : ℕ → ℕ, d 0 = 0 ∧ d 1 = c (t + 1) - c t ∧
      d N = (rotWord w (c t)).length ∧ (∀ s : ℕ, d s ≤ d (s + 1)) ∧
      ∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, d s ≤ p → p ≤ q →
        q ≤ d (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier
              (vertex (vertex v w (c t)) (rotWord w (c t)) p)
              (vertex (vertex v w (c t)) (rotWord w (c t)) q) : ℕ) : ℝ) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hctw : c t ≤ w.length := by
    have h := hmono (le_of_lt ht)
    rw [hcN] at h
    exact h
  have hlen : (rotWord w (c t)).length = w.length := length_rotWord w hctw
  set dd : ℕ → ℕ := fun s => if s ≤ N - t then c (t + s) - c t
    else c (s - (N - t)) + (w.length - c t)
  have hddv : ∀ s : ℕ, dd s = if s ≤ N - t then c (t + s) - c t
      else c (s - (N - t)) + (w.length - c t) := fun s => rfl
  have hdle : ∀ s : ℕ, s ≤ N - t → dd s = c (t + s) - c t := by
    intro s hs
    rw [hddv s, if_pos hs]
  have hdge : ∀ s : ℕ, N - t ≤ s →
      dd s = c (s - (N - t)) + (w.length - c t) := by
    intro s hs
    rcases Nat.eq_or_lt_of_le hs with heq | hlt
    · -- at the seam the two branches agree, by `c N = w.length` and `c 0 = 0`
      rw [hddv s, if_pos (le_of_eq heq.symm), ← heq,
        show t + (N - t) = N from by omega, hcN,
        show N - t - (N - t) = 0 from by omega, hc0]
      omega
    · rw [hddv s, if_neg (by omega)]
  refine ⟨dd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdle 0 (Nat.zero_le _), Nat.add_zero, Nat.sub_self]
  · rw [hdle 1 (by omega)]
  · rw [hdge N (by omega), show N - (N - t) = t from by omega, hlen]
    omega
  · intro s
    rcases Nat.lt_or_ge s (N - t) with hs | hs
    · rw [hdle s (by omega), hdle (s + 1) (by omega),
        show t + (s + 1) = t + s + 1 from by omega]
      have := hcmono (t + s)
      omega
    · rw [hdge s hs, hdge (s + 1) (by omega),
        show s + 1 - (N - t) = s - (N - t) + 1 from by omega]
      have := hcmono (s - (N - t))
      omega
  · intro s hsN hs0 p q hp hpq hq
    rcases Nat.lt_or_ge s (N - t) with hs | hs
    · -- before the seam: the old side `t + s`
      rw [hdle s (by omega)] at hp
      rw [hdle (s + 1) (by omega),
        show t + (s + 1) = t + s + 1 from by omega] at hq
      have h1 : c t ≤ c (t + s) := hmono (by omega)
      have h2 : c (t + s + 1) ≤ c N := hmono (by omega)
      have h3 : c t ≤ c (t + s + 1) := hmono (by omega)
      rw [hcN] at h2
      have hkey := hcqg (t + s) (by omega) (by omega) (c t + p) (c t + q)
        (by omega) (by omega) (by omega)
      rw [show c t + q - (c t + p) = q - p from by omega] at hkey
      rw [vertex_rotWord_le v w hctw p (by omega),
        vertex_rotWord_le v w hctw q (by omega)]
      exact hkey
    · -- past the seam: the old side `s - (N - t)`, read from the basepoint
      rw [hdge s hs] at hp
      rw [hdge (s + 1) (by omega),
        show s + 1 - (N - t) = s - (N - t) + 1 from by omega] at hq
      have h1 : c (s - (N - t) + 1) ≤ c t := hmono (by omega)
      have hrp : p - (w.length - c t) ≤ c t := by omega
      have hrq : q - (w.length - c t) ≤ c t := by omega
      have hkey := hcqg (s - (N - t)) (by omega) (by omega)
        (p - (w.length - c t)) (q - (w.length - c t)) (by omega) (by omega)
        (by omega)
      rw [show q - (w.length - c t) - (p - (w.length - c t)) = q - p
          from by omega] at hkey
      rw [vertex_rotWord_add v w hctw hclosed p (p - (w.length - c t))
          (by omega) hrp,
        vertex_rotWord_add v w hctw hclosed q (q - (w.length - c t))
          (by omega) hrq]
      exact hkey

end OsinComponents
end GGT
end GroupApproximation
