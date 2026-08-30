import GroupApproximation.GGT.DGOPolygonBaseCaseTower

/-!
# The side count tower, at every side count

`DGOPolygonBaseCaseTower.baseCase_of_sideCount` runs the recursion of Lemma 4.17
from four sides to eight, which is the range the recut of a polygon with at most
six sides asks for.  Nothing about the recursion stops there: each step is
`span_mem_relBall_of_recursionStep`, and iterating it gives the side-`0` bound at
every side count, with a constant that grows by `C` per step.

    3 ≤ N  ⟹  the exempt side-`0` bound at `N`, radius `(N - 1) · C · N`

`N = 3` is `baseCase_of_pad`, and it is the reason the coefficient is `N - 1`
rather than `N - 2` or `N - 3`: padding a triangle to a quadrilateral costs
exactly `2 · C · 3`, which is `(3 - 1) · C · 3` on the nose.  From four up the
step contributes exactly `C`, `C + (m + 3) · C = (m + 4) · C`, so the coefficient
advances by one per side and the formula is tight against the chain rather than
a weakening of it.

## What this is not

It is NOT `OsinComponents.IsolatedComponentBound`, which asks for ONE constant
covering every side count: that puts `∃ C` before `∀ n`, nothing in the tree
proves it, and its consumers were deleted for that reason.  Here the constant
comes after the side count and grows quadratically in it, which is what the
recursion actually delivers.  A consumer that needs the bound at one fixed side
count --- local finiteness of relative balls, for instance --- is served by this
and not by the uniform form.

The `n ≤ 6` cap in `DGOPolygonBaseCaseTower` is that module's instantiation
range, not an obstruction; this module removes it by induction and leaves the
constant explicit.

## Why the `n`-gon statement needs no lower bound on `n`

`baseCase_of_sideCount_ge` carries `3 ≤ N`, but the isolated-component form
below carries nothing: the recut of an `n`-gon whose component runs from side
`t` to side `t'` has `n + 2 - (t' - t)` sides, and `t' < n` with `t ≤ t'` forces
`t' - t ≤ n - 1`, so the recut side count is at least `3` WHATEVER `n` is.  At
`n = 1` it is exactly `3`, at `n = 2` it is `3` or `4`.  The one remaining case,
`n = 0`, is vacuous: `c 0 = 0 = |w|` leaves no letters, so no components.

So the short end costs nothing here, and a consumer indexing by a ball radius
--- where `n` takes every value, `n = 1` a bigon and `n = 0` a degenerate loop
--- needs no case split at the top of its own proof.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Four sides and up, by induction on the recursion step -/

/-- **The exempt side-`0` bound at `m + 4` sides**, for every `m`.

Induction on `m` over `span_mem_relBall_of_recursionStep`, carrying the constant
`(m + 3) · C`.  The step turns the constant `C₂` at `N` into `C₁ + C₂` at
`N + 1`, so with `C₁ = C` the coefficient advances by exactly one: the identity
discharged at each step is `C + (m + 3) · C = (m + 4) · C`.

The side count is carried as `m + 4` rather than as `N` with `4 ≤ N`, so that
the coefficient is an addition rather than a truncated subtraction: `ring` closes
the step, which it could not do against `N - 1`. -/
theorem baseCase_of_sideCount_add (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4)) :
    ∀ (m : ℕ) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c (m + 4) = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < m + 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam ((m + 3) * C * (m + 4)) := by
  intro m
  induction m with
  | zero =>
      intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
      exact relBall_mono_radius D lam (by omega)
        (hbase v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso)
  | succ m ih =>
      have h := span_mem_relBall_of_recursionStep D hsymm mu b hmu hb C
        ((m + 3) * C) (n := m + 1 + 4) (N := m + 4) (by omega) (by omega) hbase ih
      intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
      refine relBall_mono_radius D lam (le_of_eq ?_)
        (h v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso)
      ring

/-! ## Three sides and up -/

/-- **The exempt side-`0` bound at every side count from three up**, with the
constant `(N - 1) · C`.

`N = 3` is `baseCase_of_pad`, whose `2 · C · 3` is `(3 - 1) · C · 3`; from four
up it is `baseCase_of_sideCount_add` with `m = N - 4`, whose `(m + 3) · C` is
`(N - 1) · C`.  Neither step loses anything: the formula is what the chain
delivers, not a bound on it. -/
theorem baseCase_of_sideCount_ge (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4))
    {N : ℕ} (h3N : 3 ≤ N) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam ((N - 1) * C * N) := by
  rcases Nat.eq_or_lt_of_le h3N with h3 | h4
  · -- three sides: the padded triangle, whose `2 * C * 3` IS `(3 - 1) * C * 3`
    subst h3
    intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    rw [show (3 : ℕ) - 1 = 2 from by omega]
    exact baseCase_of_pad D mu b hb C (N := 3) rfl hbase v w c hlet hclosed hc0
      hcN hcmono lam hcqg hcomp hiso
  · -- four sides and up
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 4 := ⟨N - 4, by omega⟩
    intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    rw [show m + 4 - 1 = m + 3 from by omega]
    exact baseCase_of_sideCount_add D hsymm mu b hmu hb C hbase m v w c hlet
      hclosed hc0 hcN hcmono lam hcqg hcomp hiso

/-! ## The isolated-component bound at one side count -/

/-- **The bound for an arbitrary isolated component of an `N`-gon**, at every
`N`, from the four-sided base case.

The component may sit anywhere: interior to a side, straddling a corner, or
straddling several.  The recut turns it into the side `0` of an
`(N + 2 - (t' - t))`-gon, which `baseCase_of_sideCount_ge` bounds, and
`N + 2 - (t' - t)` lies in `[3, N + 2]` for every `N` --- see the module header.
The radius is absolute, not of the form `C · N`: a consumer that fixes `N` first
never divides by it. -/
theorem isolatedComponentBound_nGon_of_baseCase (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4))
    (N : ℕ) :
    ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D mu b N v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k
          ∈ D.relBall nu ((N + 1) * C * (N + 2)) := by
  intro v u hpoly nu i k hcomp hiso
  obtain ⟨hlet, hclosed, c, hc0, hcn, hcmono, hcqg⟩ := hpoly
  have hik : i < k := hcomp.1
  have hku : k ≤ u.length := hcomp.2.1
  have hN1 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · exact absurd hcn (by omega)
    · exact hpos
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  obtain ⟨t, ht, hti, hit⟩ := exists_side_of_index c hc0 N i hN1 (by omega)
  obtain ⟨t', ht', htk, hkt'⟩ := exists_side_of_index c hc0 N k hN1 (by omega)
  have htt' : t ≤ t' := by
    by_contra hcon
    have h : c (t' + 1) ≤ c t := hmono (by omega)
    omega
  -- the recut side count is in `[3, N + 2]`, so one constant covers it
  have hbaseN : ∀ (v' : G) (w' : List (RelLetter G Λ)) (c' : ℕ → ℕ),
      (∀ a ∈ w', D.IsLetter a) → RelLetter.listVal w' = 1 → c' 0 = 0 →
      c' (N + 2 - (t' - t)) = w'.length → (∀ s : ℕ, c' s ≤ c' (s + 1)) →
      ∀ lam : Λ,
      (∀ s : ℕ, s < N + 2 - (t' - t) → s ≠ 0 → ∀ p q : ℕ, c' s ≤ p → p ≤ q →
        q ≤ c' (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v' w' p)
              (vertex v' w' q) : ℕ) : ℝ)) →
      IsComp lam w' (c' 0) (c' 1) → IsIsolated D.fam lam v' w' (c' 0) →
        (vertex v' w' (c' 0))⁻¹ * vertex v' w' (c' 1)
          ∈ D.relBall lam ((N + 1) * C * (N + 2 - (t' - t))) := by
    intro v' w' c' hlet' hclosed' hc0' hcN' hcmono' lam' hcqg' hcomp' hiso'
    exact relBall_mono_radius D lam'
      (Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl)
      (baseCase_of_sideCount_ge D hsymm mu b hmu hb C hbase
        (N := N + 2 - (t' - t)) (by omega) v' w' c' hlet' hclosed' hc0' hcN'
        hcmono' lam' hcqg' hcomp' hiso')
  have hkey := isolatedComponent_span_of_baseCase D mu b ((N + 1) * C) ht hti hit
    ht' htk hkt' htt' hbaseN hlet hclosed hc0 hcn hcmono hcqg hcomp hiso
  exact relBall_mono_radius D nu (Nat.mul_le_mul le_rfl (by omega)) hkey

/-- **The `n`-gon bound from four-point hyperbolicity alone**, at `(1,b)`.

`DGOIsolatedComponentSideZero.baseCase_of_sideZero_at` discharges the binder
above with dgo-cycle's four-sided base case, whose constant is
`25 (δ + b + 1)`. -/
theorem isolatedComponentBound_nGon_of_fourPointHyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (N : ℕ) :
    ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 (b : ℝ) N v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k
          ∈ D.relBall nu ((N + 1) * (25 * (δ + b + 1)) * (N + 2)) :=
  isolatedComponentBound_nGon_of_baseCase D hsymm 1 (b : ℝ) le_rfl
    (Nat.cast_nonneg b) (25 * (δ + b + 1))
    (baseCase_of_sideZero_at D hsymm hδ (b := b) rfl) N

/-- **The same, as a radius that exists.**  The shape a local-finiteness
consumer takes: it fixes the side count first and needs only SOME radius. -/
theorem exists_isolatedComponentBound_nGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (N : ℕ) :
    ∃ R : ℕ, ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 (b : ℝ) N v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu R :=
  ⟨(N + 1) * (25 * (δ + b + 1)) * (N + 2),
    isolatedComponentBound_nGon_of_fourPointHyperbolic D hsymm b hδ N⟩

end OsinComponents
end GGT
end GroupApproximation
