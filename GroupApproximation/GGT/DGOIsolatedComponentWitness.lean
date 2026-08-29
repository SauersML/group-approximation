import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# The isolated-component bound is not vacuous

`OsinComponents.IsolatedComponentBound` quantifies over quasi-geodesic polygons
carrying an isolated component.  `isQuasiGeodesicPolygon_nil` shows the polygon
predicate is inhabited, but the empty path has no components at all, so it does
not show that the bound says anything.  This module supplies a polygon that
does: one with an isolated component whose span is a prescribed nontrivial
element of `H lam`.

## Any closed path is a quasi-geodesic `1`-gon, at `b = |w|`

`isQuasiGeodesicPolygon_of_closed`: the lower bound a quasi-geodesic side must
satisfy is `(j - i)/μ - b ≤ d(vertex i, vertex j)`, and at `μ = 1`, `b = |w|`
its left side is at most `0` while the right side is a distance.  So the
predicate imposes nothing at that constant, and the whole content of
`IsolatedComponentBound` is what happens as `|w|` grows past `b`.

This is worth recording rather than working around: it shows the bound cannot be
proved by any argument that treats `(μ, b)` as controlling `|w|`, and it makes
the witness below cheap, since no distance in `Γ(G, X ⊔ ℋ)` has to be computed.

## The witness

For `h ∈ H lam` with `h⁻¹ ∈ X` and `h ≠ 1`, read from `1`:

    w = [comp lam h, base h⁻¹] .

It is closed, both letters are admissible, and its only `H lam`-component is the
first letter, so that component is isolated for want of any other.  Its span is

    (vertex 1 w 0)⁻¹ * (vertex 1 w 1) = h ≠ 1 ,

so the bound's conclusion is a nonvacuous assertion about `h`: it puts `h` in
`D.relBall lam (C * 1)`.  Here that is true for `C ≥ 1`, `h⁻¹` being a letter of
`X`, which is the consistency check the witness is for.

The hypotheses are the weakest that make the word admissible; they hold for
instance whenever `D.base = Set.univ`, and then for every nontrivial `h` of
every `H lam`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  Closed paths are quasi-geodesic at `b = |w|` -/

/-- **Every closed admissible path is a `(1, |w|)`-quasi-geodesic `1`-gon.**  The
quasi-geodesic clause asks `(j - i)/μ - b ≤ d`, and at `μ = 1`, `b = |w|` the
left side is at most `0`. -/
theorem isQuasiGeodesicPolygon_of_closed (D : RelGenSet G Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) :
    IsQuasiGeodesicPolygon D 1 (w.length : ℝ) 1 v w := by
  refine ⟨hlet, hclosed, fun s => w.length * s, by simp, by simp, ?_, ?_⟩
  · intro s
    exact Nat.mul_le_mul le_rfl (Nat.le_succ s)
  · intro s hs i j _ hij hj
    have hs0 : s = 0 := by omega
    subst hs0
    have hj' : j ≤ w.length := by simpa using hj
    have hsub : ((j - i : ℕ) : ℝ) ≤ (w.length : ℝ) := by
      have hle : (j - i : ℕ) ≤ w.length := by omega
      exact_mod_cast hle
    have hd : (0 : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [div_one]
    linarith

/-! ## 2.  A polygon with an isolated component of prescribed span -/

/-- **The two-letter polygon.**  Its first letter is an `H lam`-component, its
second is a letter of `X`, and there is no other component, so the first is
isolated. -/
theorem exists_isolated_component_of_mem (D : RelGenSet G Λ) (lam : Λ) {h : G}
    (hh : h ∈ D.fam lam) (hinv : h⁻¹ ∈ D.base) (hne : h ≠ 1) :
    ∃ (b : ℝ) (w : List (RelLetter G Λ)), 0 ≤ b ∧
      IsQuasiGeodesicPolygon D 1 b 1 1 w ∧
      IsComp lam w 0 1 ∧ IsIsolated D.fam lam 1 w 0 ∧
      (vertex (1 : G) w 0)⁻¹ * vertex (1 : G) w 1 ≠ 1 := by
  classical
  set w : List (RelLetter G Λ) :=
    [RelLetter.comp lam h, RelLetter.base h⁻¹] with hw
  have hlen : w.length = 2 := by rw [hw]; rfl
  have hlet : ∀ a ∈ w, D.IsLetter a := by
    rw [hw]
    refine List.forall_mem_cons.mpr ⟨hh, ?_⟩
    exact List.forall_mem_singleton.mpr hinv
  have hclosed : RelLetter.listVal w = 1 := by
    rw [hw]
    simp only [RelLetter.listVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, RelLetter.val]
    group
  -- the first letter is a component, the second is not
  have hzero : ∀ hj : (0 : ℕ) < w.length, (w[0]'hj).IsCompOf lam := by
    intro _
    exact rfl
  have hone : ∀ hk : (1 : ℕ) < w.length, ¬ (w[1]'hk).IsCompOf lam := by
    intro _
    exact fun hc => hc
  have hcomp : IsComp lam w 0 1 := by
    refine ⟨Nat.zero_lt_one, by omega, ?_, ?_, hone⟩
    · intro j _ hj1 hjw
      have hj0 : j = 0 := by omega
      subst hj0
      exact hzero hjw
    · intro j hj
      exact absurd hj (by omega)
  -- there is no other component
  have hstart : ∀ j : ℕ, IsCompStart lam w j → j = 0 := by
    rintro j ⟨k, hik, hkw, -, hprev, -⟩
    by_contra hj0
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + 1 := by
      cases j with
      | zero => exact absurd rfl hj0
      | succ m => exact ⟨m, rfl⟩
    have hm : m = 0 := by omega
    subst hm
    exact hprev 0 rfl (by omega) (hzero (by omega))
  refine ⟨(w.length : ℝ), w, Nat.cast_nonneg _,
    isQuasiGeodesicPolygon_of_closed D 1 hlet hclosed, hcomp,
    ⟨⟨1, hcomp⟩, ?_⟩, ?_⟩
  · intro j hj hjs
    exact absurd (hstart j hjs) hj
  · have h0 : vertex (1 : G) w 0 = 1 := vertex_zero _ _
    have h1 : vertex (1 : G) w 1 = h := by
      show (1 : G) * h = h
      rw [one_mul]
    rw [h0, h1, inv_one, one_mul]
    exact hne

end OsinComponents
end GGT
end GroupApproximation
