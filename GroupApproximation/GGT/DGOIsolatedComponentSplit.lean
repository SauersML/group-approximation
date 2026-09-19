import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# Splitting a span: the composition calculus behind Lemma 4.17

Where Dahmani--Guirardel--Osin cannot exclude a coset hit (their Lemma 4.17, the
cut through the polygon), they do not discard the offending connector: they
*split*, writing the span of the distinguished component as a product of two
spans, one isolated in an `(n-1)`-gon and one isolated in a `4`-gon, and add the
two bounds.  Their recursion `s(n) ≤ n (s(n-1) + s(4))` is that split applied
once per side, plus the triangle inequality for `d̂_lam`.

This module supplies the composition calculus, unconditionally.  The geometry ---
that the split exists --- is not here and is not assumed here: a caller who has
produced the two memberships gets the composite bound, and the constant it gets
is the one the recursion names.

Concept grep before writing: `relBall_mul`, `triangle`, `split` across the tree.
`relBall_mul` (OsinSeparatingCosets) is the group-level statement that radii add;
it is stated for `h₁ * h₂` and is applied here at differences of vertices, which
is the form every polygon argument produces.  No chained version exists.

## What is proved

* `span_mem_relBall_of_split` --- the triangle inequality for `d̂_lam`, written at
  three points: `x⁻¹z = (x⁻¹y)(y⁻¹z)`.
* `span_mem_relBall_of_chain` --- its `N`-fold form: `N` steps of radius `r` give
  radius `N * r`.  This is the `n` in `s(n) ≤ n (…)`.
* `relBall_mul_sides` --- the constant arithmetic of one split:
  `C₁ · 4 + C₂ · (n-1) ≤ (C₁ + C₂) · n` for `n ≥ 4`, so a split against the
  `4`-gon case and the `(n-1)`-gon case stays of the form `C · n`.
* `relBall_chain_sides` --- the two together, in the shape of the recursion: `n`
  steps, each split into a `4`-gon part and an `(n-1)`-gon part, give
  `(C₁ + C₂) · n · n`.

Nothing here needs hyperbolicity, a polygon, or isolation.  What it needs is that
`d̂_lam` is a left-invariant metric on `H lam`, which is `relBall_mul` together
with `one_mem_relBall`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The triangle inequality, at three points -/

/-- **`d̂_lam` obeys the triangle inequality at three points.**  The two spans
compose: `x⁻¹z = (x⁻¹y)(y⁻¹z)`, and `relBall_mul` adds the radii. -/
theorem span_mem_relBall_of_split (D : RelGenSet G Λ) (lam : Λ) {x y z : G}
    {N M : ℕ} (h1 : x⁻¹ * y ∈ D.relBall lam N) (h2 : y⁻¹ * z ∈ D.relBall lam M) :
    x⁻¹ * z ∈ D.relBall lam (N + M) := by
  have h3 := relBall_mul D lam h1 h2
  have hrw : (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z := by group
  rwa [hrw] at h3

/-! ## The chained form -/

/-- **`N` steps of radius `r` give radius `N * r`.**

This is the factor `n` in Dahmani--Guirardel--Osin's `s(n) ≤ n (s(n-1) + s(4))`:
their split is applied once per side of the polygon, and the resulting spans
compose along the chain of intermediate points. -/
theorem span_mem_relBall_of_chain (D : RelGenSet G Λ) (lam : Λ) (y : ℕ → G)
    (r : ℕ) : ∀ N : ℕ,
      (∀ t : ℕ, t < N → (y t)⁻¹ * y (t + 1) ∈ D.relBall lam r) →
        (y 0)⁻¹ * y N ∈ D.relBall lam (N * r) := by
  intro N
  induction N with
  | zero =>
      intro _
      rw [inv_mul_cancel]
      exact one_mem_relBall D lam _
  | succ N ih =>
      intro h
      have h1 := ih (fun t ht => h t (by omega))
      have h2 := h N (by omega)
      have h3 := span_mem_relBall_of_split D lam h1 h2
      have hlen : N * r + r = (N + 1) * r := by ring
      rwa [hlen] at h3

/-! ## The constants of one split -/

/-- **A split against the `4`-gon case and the `(n-1)`-gon case stays of the form
`C · n`.**  For `n ≥ 4`, `C₁ · 4 + C₂ · (n-1) ≤ (C₁ + C₂) · n`. -/
theorem relBall_mul_sides (D : RelGenSet G Λ) (lam : Λ) {x y z : G}
    {C₁ C₂ n : ℕ} (hn : 4 ≤ n) (h1 : x⁻¹ * y ∈ D.relBall lam (C₁ * 4))
    (h2 : y⁻¹ * z ∈ D.relBall lam (C₂ * (n - 1))) :
    x⁻¹ * z ∈ D.relBall lam ((C₁ + C₂) * n) := by
  refine relBall_mono_radius D lam ?_ (span_mem_relBall_of_split D lam h1 h2)
  have e1 : C₁ * 4 ≤ C₁ * n := Nat.mul_le_mul le_rfl hn
  have e2 : C₂ * (n - 1) ≤ C₂ * n := Nat.mul_le_mul le_rfl (by omega)
  calc C₁ * 4 + C₂ * (n - 1) ≤ C₁ * n + C₂ * n := Nat.add_le_add e1 e2
    _ = (C₁ + C₂) * n := by ring

/-! ## The recursion -/

/-- **Dahmani--Guirardel--Osin's Lemma 4.17 recursion, as a bound on constants.**

`n` steps, each of which splits into a part bounded by the `4`-gon case and a
part bounded by the `(n-1)`-gon case, compose to `(C₁ + C₂) · n · n`.  That is
`s(n) ≤ n (s(n-1) + s(4))` with `s(m) = C · m`: the outer `n` is the number of
steps, the inner one the number of sides.

The hypothesis is exactly what a proof of the split has to produce, and no more:
for each step, *some* intermediate point with the two memberships.  It is not a
statement about polygons, so it cannot smuggle one in. -/
theorem relBall_chain_sides (D : RelGenSet G Λ) (lam : Λ) (y : ℕ → G)
    {C₁ C₂ n : ℕ} (hn : 4 ≤ n)
    (h : ∀ t : ℕ, t < n → ∃ u : G, (y t)⁻¹ * u ∈ D.relBall lam (C₁ * 4) ∧
      u⁻¹ * y (t + 1) ∈ D.relBall lam (C₂ * (n - 1))) :
    (y 0)⁻¹ * y n ∈ D.relBall lam ((C₁ + C₂) * n * n) := by
  have hstep : ∀ t : ℕ, t < n →
      (y t)⁻¹ * y (t + 1) ∈ D.relBall lam ((C₁ + C₂) * n) := by
    intro t ht
    obtain ⟨u, hu1, hu2⟩ := h t ht
    exact relBall_mul_sides D lam hn hu1 hu2
  have hchain := span_mem_relBall_of_chain D lam y ((C₁ + C₂) * n) n hstep
  rwa [Nat.mul_comm n ((C₁ + C₂) * n)] at hchain

end OsinComponents
end GGT
end GroupApproximation
