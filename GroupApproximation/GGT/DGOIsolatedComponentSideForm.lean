import GroupApproximation.GGT.DGOIsolatedComponentRotateCut
import GroupApproximation.GGT.DGOIsolatedComponentStraddle

/-!
# From the base case at side `0` to the side form at side `t`

Dahmani--Guirardel--Osin's Lemma 4.16 is proved with the distinguished component
as the *first* side.  The recut of `DGOIsolatedComponentStraddle` delivers it as
the side `t`.  This module closes that distance, and it is the last step of the
§4.2 chain that is not geometry:

    base case at side 0  ⟹  side form at side t

by rotating the closed polygon so that side `t` comes first
(`DGOIsolatedComponentRotate`, `…RotateCut`).  The rotation keeps the span
*exactly* — it is the same group element throughout, so no `d̂_lam` estimate is
transported — and keeps isolation.

Composed with `span_mem_relBall_of_sideForm_straddle`, this gives Osin's Lemma 4.2
form for an isolated component of a `(μ,b)`-quasi-geodesic `n`-gon from the base
case alone: `isolatedComponent_span_of_baseCase`.

## What the base case must deliver, exactly

    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N)

`dgo-cycle`'s `span_mem_relBall_of_sideZero` is this at `N = 4`, `μ = 1` and
their `b`, with `C := 25 * (δ + b + 1)`; the two differences are that they bind
`lam` after the clause rather than before it, and that their constant is written
`100 * (δ + b + 1)` rather than `C * N`.  The adapter is therefore one term:

    fun v w c hlet hcl h0 hN hm lam hclause hcomp hiso => by
      simpa [show 25 * (δ + b + 1) * 4 = 100 * (δ + b + 1) from by ring] using
        span_mem_relBall_of_sideZero D hsymm hδ v w c hlet hcl h0 hN hm hclause
          lam hcomp hiso

Their `baseCase_of_sideZero` is the same theorem pre-adapted to the *previous*
shape of this binder, which carried `c 1 = 1` and named the component at the
literal indices `0`, `1`; with the collapse now theirs, that hypothesis is gone
and the component is named at `c 0`, `c 1`, as `span_mem_relBall_of_sideZero`
itself does.

Three things about the shape, each settled by an earlier round rather than
chosen here.

*`N` is fixed, not `∀ N ≤ 6`.*  The base case is taken at the ONE side count the
polygon has, so a base case proved only at `N = 4` is usable.  Through the recut
that covers a component which is a whole side (no recut needed) and one which
straddles two corners (the recut yields four sides); the counts are
`n + 2 - (t' - t)`.

*No `c 1 = 1`.*  The distinguished side may be a run of any length: dgo-cycle's
`exists_short_isolating_cycle` collapses it internally through
`exists_unit_side_zero`.  `DGOIsolatedComponentCollapseCut` therefore does not
appear in this chain; it remains correct and is kept for a base case that wants
the collapse done for it.

*The clause on `s ≠ 0` only.*  Dahmani--Guirardel--Osin's Definition 4.13.  With
the clause on every side the side form is false for a run straddling a corner,
since all of a run's vertices are within one letter of each other.

## The two degenerate cases, which are where the work is

*The component is the whole closed word* (`c t = 0` and `c (t+1) = w.length`).
Then its span is `v⁻¹ * v = 1`, which lies in every relative ball, and no
rotation happens.  This case has to be taken first, because it is exactly the
case in which the rotation's hypothesis `hwrap` is false: the letter at `0` is a
`lam`-letter of the component itself.

*The component starts at the basepoint but does not fill the word* (`c t = 0`,
`c (t+1) < w.length`).  Then `hwrap` holds vacuously.  Only when `c t > 0` is
`notMem_wrap_of_isIsolated` used, and it is there that closedness plus isolation
rule out a run continuing past the basepoint.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The transfer -/

/-- **The side form follows from the base case at side `0`.**

The hypothesis is Lemma 4.16 in the shape it is proved: distinguished component
the first side, the quasi-geodesic clause asked only of the sides `s ≠ 0`.  The
conclusion is the same statement with the component at an arbitrary side `t`.
Both are at the same side count `N`, so a base case proved at one `N` is usable
at that `N`. -/
theorem sideForm_of_baseCase (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ) {N : ℕ}
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N)) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ (lam : Λ) (t : ℕ), t < N →
      (∀ s : ℕ, s < N → s ≠ t → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c t) (c (t + 1)) → IsIsolated D.fam lam v w (c t) →
        (vertex v w (c t))⁻¹ * vertex v w (c (t + 1))
          ∈ D.relBall lam (C * N) := by
  intro v w c hlet hclosed hc0 hcN hcmono lam t ht hcqg hcomp hiso
  have hik : c t < c (t + 1) := hcomp.1
  have hkw : c (t + 1) ≤ w.length := hcomp.2.1
  have hiw : c t ≤ w.length := by omega
  -- the component filling the whole closed word has trivial span
  by_cases hwhole : c t = 0 ∧ c (t + 1) = w.length
  · obtain ⟨hi0, hkl⟩ := hwhole
    have hone : (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) = 1 := by
      rw [hi0, hkl, vertex_zero, vertex_length_of_closed v w hclosed,
        inv_mul_cancel]
    rw [hone]
    exact one_mem_relBall D lam _
  -- otherwise the run does not continue past the basepoint
  have hwrap : ∀ h0 : 0 < w.length, c (t + 1) = w.length →
      ¬ (w[0]'h0).IsCompOf lam := by
    rcases Nat.eq_zero_or_pos (c t) with hi0 | hipos
    · intro _ hkl
      exact absurd ⟨hi0, hkl⟩ hwhole
    · exact notMem_wrap_of_isIsolated D lam v hlet hclosed hcomp hiso hipos
  -- rotate, so that the component is the first side
  obtain ⟨d, hd0, hd1, hdN, hdmono, hdqg⟩ :=
    exists_rot_cut D mu b hclosed hc0 hcN hcmono ht hcqg
  have hv0 : vertex (vertex v w (c t)) (rotWord w (c t)) 0 = vertex v w (c t) := by
    rw [vertex_rotWord_le v w hiw 0 (Nat.zero_le _), Nat.add_zero]
  have hvK : vertex (vertex v w (c t)) (rotWord w (c t)) (c (t + 1) - c t)
      = vertex v w (c (t + 1)) := by
    rw [vertex_rotWord_le v w hiw (c (t + 1) - c t) (by omega),
      show c t + (c (t + 1) - c t) = c (t + 1) from by omega]
  have hgoal := hbase (vertex v w (c t)) (rotWord w (c t)) d
    (letters_rotWord D hlet (c t)) (listVal_rotWord w (c t) hclosed) hd0 hdN
    hdmono lam hdqg
    (by rw [hd0, hd1]; exact isComp_rotWord lam hcomp hiw hwrap)
    (by rw [hd0]; exact isIsolated_rotWord D lam v hlet hclosed hcomp hiso hwrap)
  rw [hd0, hd1, hv0, hvK] at hgoal
  exact hgoal

/-! ## The whole chain, in one statement -/

/-- **Osin's Lemma 4.2 form, from the base case alone.**

The first binder is Dahmani--Guirardel--Osin's Lemma 4.16 in the shape it is
proved, at the side count the recut produces.  The conclusion is the bound for an
isolated component of a `(μ,b)`-quasi-geodesic `n`-gon lying between the sides `t`
and `t'`: no requirement that it be a side, or a single letter, and no constant
lost beyond the `n ↦ n + 2 - (t' - t)` of the recut.

The chain is `span_mem_relBall_of_sideForm_straddle ∘ sideForm_of_baseCase`:
recut the polygon so the component is a side (exempt from the clause, which is
what makes a straddling run harmless), turn it round so that side comes first,
and quote the base case.  The span is the same group element at every step. -/
theorem isolatedComponent_span_of_baseCase (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ)
    {n : ℕ} {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {lam : Λ}
    {i k t t' : ℕ} (ht : t < n) (hti : c t ≤ i) (hit : i ≤ c (t + 1))
    (ht' : t' < n) (htk : c t' ≤ k) (hkt' : k ≤ c (t' + 1)) (htt' : t ≤ t')
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c (n + 2 - (t' - t)) = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < n + 2 - (t' - t) → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam (C * (n + 2 - (t' - t))))
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < n → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k
      ∈ D.relBall lam (C * (n + 2 - (t' - t))) :=
  span_mem_relBall_of_sideForm_straddle D mu b C ht hti hit ht' htk hkt' htt'
    (sideForm_of_baseCase D mu b C hbase) hlet hclosed hc0 hcn hcmono hcqg hcomp
    hiso

end OsinComponents
end GGT
end GroupApproximation
