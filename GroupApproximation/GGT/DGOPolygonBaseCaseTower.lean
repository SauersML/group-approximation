import GroupApproximation.GGT.DGOPolygonLemma417
import GroupApproximation.GGT.DGOIsolatedComponentSideForm
import GroupApproximation.GGT.DGOIsolatedComponentSideZero

/-!
# The tower of side counts, and the isolated-component bound it gives

`DGOPolygonLemma417` turns the base case at four sides into the bound at five,
six, and --- one line per step --- any number of sides.  What the recut of
`DGOIsolatedComponentStraddle` asks for is the base case at
`n + 2 - (t' - t)`, which for an `n`-gon with `n ≤ 6` ranges over `3 … 8`.  This
module supplies exactly that range, with one constant:

    3 ≤ N ≤ 8  ⟹  the exempt side-`0` bound at `N`, with radius `5 · C · N`

the three-sided end by padding a trivial fourth side (`baseCase_of_pad`, moved
here from the held general-position module, which nothing else in the tree
uses), the rest by the recursion step.

Composed with `isolatedComponent_span_of_baseCase` this is Dahmani--Guirardel--
Osin's Lemma 4.16 for a `(1,0)`-quasi-geodesic polygon of at most six sides and
an *arbitrary* isolated component --- not required to be a side, a single
letter, or to avoid the corners.

## The one fact about position that is used

`exists_side_of_index`: an index at most `c n` lies on some side.  That is the
whole of what the recut needs to locate the component, and it is a statement
about a monotone `c`, not about the polygon: the general-position construction
(choosing a corner offset) is a different and harder thing, and is not used
here.

## Where the `(μ,b)` genericity comes from

The chain is generic in `(μ,b)`, and it is cheap for two reasons.

*The recut and side-form chain was already generic.*
`DGOIsolatedComponent{Recut,Straddle,Rotate,RotateCut,SideForm}` and
`DGOPolygonJoin` have always been stated with `(mu b : ℝ)` free.

*Lemma 4.17 never reads the clause of the sides it inherits.*  Sides `1 … n-1`
of the original polygon are quoted verbatim into the cut polygons and used only
as clause-suppliers.  In particular `isComp_eq_succ_of_geodesic` --- components
of a geodesic word are single letters, which is exactly what fails when a side
is only `(μ,b)`-quasi-geodesic --- is not used anywhere in this chain, and
neither is any `IsGeodesicChain` statement.

The only metric input is the CHORD, which the proof builds itself with
`existsGeodesicWord` and which is geodesic whatever the sides are.  It is read
three times, each `sub_le_wordDist_vertex` applied to `q`: the chord component
is the chord's last letter; a component start on the far polygon's chord block
has index at most one; one on the edge polygon's chord block has index `t - 1`.
Where those three deliver the chord's own side of a cut polygon, the clause is
discharged by

    x / mu - b ≤ x / mu ≤ x ≤ d        (`sub_le_self`, then `div_le_self`)

and that is the whole arithmetic cost of the generalisation: every other clause
in the chain is quoted rather than proved.

The constants are untouched by it.  They come from the recursion (`C₁ + C₂` per
step) and from this file's slack (`5·C` over the tower, `15·C` over the recut),
never from `μ` or `b`: a base case at `(μ,b)` with radius `C · 4` yields
`(C₁ + C₂) · n` exactly as at `(1,0)`.

## What is still assumed

The base case, and nothing else.  `isolatedComponentBound_of_sideZeroBase` takes
it as a binder at `(μ,b)`, and `isolatedComponentBound_of_fourPointHyperbolic_at`
discharges that binder at `(1,b)` with
`DGOIsolatedComponentBoundFourGon.span_mem_relBall_of_sideZero`, which is proved
there from a symmetric base and four-point hyperbolicity, with constant
`25 (δ + b + 1)` off their `12δ + 2b` thinness.  A base case at general `μ` ---
Dahmani--Guirardel--Osin's Lemma 4.15, quasi-geodesic stability at
`θ = ϰ(μ,b) + 2δ`, inside their 4.16 --- instantiates the same binder and gives
the same conclusion at `(μ,b)`, with nothing here to change.

`n ≤ 6` stays.  Each step of Lemma 4.17 costs `C ↦ C₁ + C₂`, so iterating to `n`
sides gives a radius quadratic in `n`, and the linear form `C · n` at a fixed
`C` for ALL `n` --- which is what `OsinComponents.IsolatedComponentBound` asks
--- is out of reach of the recursion.  That is why Dahmani--Guirardel--Osin
prove their Lemma 4.16 by the corner-offset construction and use 4.17 only to
extend it to boundedly many sides.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Padding a triangle to a quadrilateral -/

/-- **A base case at four sides gives one at three.**

The `3`-gon is padded with a trivial fourth side at `w.length`; the clause on it
is vacuous, since its two ends coincide.  Dahmani--Guirardel--Osin allow trivial
sides in Definition 4.13 for exactly this reason.  The constant doubles rather
than being tracked exactly: `C * 4 ≤ 2 * C * 3`. -/
theorem baseCase_of_pad (D : RelGenSet G Λ) (mu b : ℝ) (hb : 0 ≤ b) (C : ℕ)
    {N : ℕ} (hN : N = 3)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4)) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam (2 * C * N) := by
  subst hN
  intro v w c hlet hclosed hc0 hc3 hcmono lam hcqg hcomp hiso
  -- the padded cut function: one trivial side at the end
  set e : ℕ → ℕ := fun s => if s ≤ 3 then c s else w.length
  have hev : ∀ s : ℕ, e s = if s ≤ 3 then c s else w.length := fun s => rfl
  have hele : ∀ s : ℕ, s ≤ 3 → e s = c s := by
    intro s hs
    rw [hev s, if_pos hs]
  have hegt : ∀ s : ℕ, 3 < s → e s = w.length := by
    intro s hs
    rw [hev s, if_neg (by omega)]
  have he0 : e 0 = 0 := by rw [hele 0 (by omega), hc0]
  have he1 : e 1 = c 1 := hele 1 (by omega)
  have he4 : e 4 = w.length := hegt 4 (by omega)
  have hemono : ∀ s : ℕ, e s ≤ e (s + 1) := by
    intro s
    rcases Nat.lt_or_ge s 3 with hs | hs
    · rw [hele s (by omega), hele (s + 1) (by omega)]
      exact hcmono s
    · rcases Nat.eq_or_lt_of_le hs with hs3 | hs3
      · exact le_of_eq (by
          rw [hele s (by omega), hegt (s + 1) (by omega), ← hs3, hc3])
      · exact le_of_eq (by rw [hegt s hs3, hegt (s + 1) (by omega)])
  have heqg : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, e s ≤ p → p ≤ q →
      q ≤ e (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p)
            (vertex v w q) : ℕ) : ℝ) := by
    intro s hs hs0 p q hp hpq hq
    rcases Nat.lt_or_ge s 3 with hs3 | hs3
    · rw [hele s (by omega)] at hp
      rw [hele (s + 1) (by omega)] at hq
      exact hcqg s hs3 hs0 p q hp hpq hq
    · -- the padded side is trivial: `p = q = w.length`
      have hs3' : s = 3 := by omega
      rw [hs3'] at hp
      rw [hele 3 le_rfl, hc3] at hp
      rw [hegt (s + 1) (by omega)] at hq
      have hpq0 : q - p = 0 := by omega
      rw [hpq0, Nat.cast_zero, zero_div]
      have h1 : (0 : ℝ) ≤ ((wordDist D.alphabet.carrier (vertex v w p)
          (vertex v w q) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hgoal := hbase v w e hlet hclosed he0 he4 hemono lam heqg
    (by rw [he0, he1, ← hc0]; exact hcomp) (by rw [he0, ← hc0]; exact hiso)
  rw [he0, he1, ← hc0] at hgoal
  exact relBall_mono_radius D lam (by omega) hgoal

/-! ## Every side count from three to eight -/

/-- **The base case at four sides gives it at every side count the recut can
ask for.**

`3` by padding, `4` by hypothesis, `5 … 8` by the recursion step of Lemma 4.17,
one step each.  The constants of the chain are `2C, C, 2C, 3C, 4C, 5C`; `5 · C`
dominates all six, so the statement carries one constant. -/
theorem baseCase_of_sideCount (D : RelGenSet G Λ)
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
    {N : ℕ} (h3N : 3 ≤ N) (hN8 : N ≤ 8) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam (5 * C * N) := by
  have h7 := span_mem_relBall_of_recursionStep D hsymm mu b hmu hb C
    (C + (C + C)) (n := 7) (N := 6) (by omega) (by omega) hbase
    (span_mem_relBall_of_sixGon D hsymm mu b hmu hb C hbase)
  interval_cases N
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (baseCase_of_pad D mu b hb C (N := 3) rfl hbase v w c hlet hclosed hc0
        hcN hcmono lam hcqg hcomp hiso)
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (hbase v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso)
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (span_mem_relBall_of_fiveGon D hsymm mu b hmu hb C hbase v w c hlet
        hclosed hc0 hcN
        hcmono lam hcqg hcomp hiso)
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (span_mem_relBall_of_sixGon D hsymm mu b hmu hb C hbase v w c hlet
        hclosed hc0 hcN
        hcmono lam hcqg hcomp hiso)
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (h7 v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso)
  · intro v w c hlet hclosed hc0 hcN hcmono lam hcqg hcomp hiso
    exact relBall_mono_radius D lam (by omega)
      (span_mem_relBall_of_recursionStep D hsymm mu b hmu hb C
        (C + (C + (C + C)))
        (n := 8) (N := 7) (by omega) (by omega) hbase h7 v w c hlet
        hclosed hc0 hcN hcmono lam hcqg hcomp hiso)

/-! ## The side an index lies on -/

/-- **An index at most `c n` lies on a side.**  The largest `t < n` with
`c t ≤ i` works: the next corner is past `i`, or is the last one. -/
theorem exists_side_of_index (c : ℕ → ℕ) (hc0 : c 0 = 0) :
    ∀ (n i : ℕ), 0 < n → i ≤ c n → ∃ t : ℕ, t < n ∧ c t ≤ i ∧ i ≤ c (t + 1) := by
  intro n
  induction n with
  | zero =>
      intro i hn _
      exact absurd hn (by omega)
  | succ n ih =>
      intro i _ hi
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨0, by omega, by omega, hi⟩
      · rcases Nat.lt_or_ge (c n) i with hlt | hle
        · exact ⟨n, by omega, by omega, hi⟩
        · obtain ⟨t, ht, ht1, ht2⟩ := ih i hn hle
          exact ⟨t, by omega, ht1, ht2⟩

/-! ## Osin's Lemma 4.2 form, from the base case at four sides -/

/-- **The isolated-component bound for a `(1,0)`-quasi-geodesic polygon of at
most six sides**, from the base case at four sides.

The component may sit anywhere: interior to a side, straddling a corner, or
straddling several.  The recut of `DGOIsolatedComponentStraddle` turns it into a
side of an `(n + 2 - (t' - t))`-gon, `baseCase_of_sideCount` supplies the base
case there, and `5 · C · (n + 2 - (t' - t)) ≤ 15 · C · n` for `1 ≤ n`. -/
theorem isolatedComponent_span_of_sideZeroBase (D : RelGenSet G Λ)
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
    {n : ℕ} (hn6 : n ≤ 6) {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    {lam : Λ} {i k t t' : ℕ} (ht : t < n) (hti : c t ≤ i) (hit : i ≤ c (t + 1))
    (ht' : t' < n) (htk : c t' ≤ k) (hkt' : k ≤ c (t' + 1)) (htt' : t ≤ t')
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < n → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (15 * C * n) := by
  have hkey := isolatedComponent_span_of_baseCase D mu b (5 * C) ht hti hit ht'
    htk hkt' htt'
    (baseCase_of_sideCount D hsymm mu b hmu hb C hbase
      (N := n + 2 - (t' - t)) (by omega)
      (by omega))
    hlet hclosed hc0 hcn hcmono hcqg hcomp hiso
  refine relBall_mono_radius D lam ?_ hkey
  calc 5 * C * (n + 2 - (t' - t)) ≤ 5 * C * (3 * n) :=
        Nat.mul_le_mul le_rfl (by omega)
    _ = 15 * C * n := by ring

/-- **The same, packaged as `IsQuasiGeodesicPolygon`.**

This is the `(μ,b) = (1,0)` instance of the `hbound` binder of
`DGOIsolatedComponentCut.connector_mem_relBall`, with `C := 15 · C`.  The side
the component starts and ends on is located by `exists_side_of_index`; a polygon
with no sides has no letters, so no components, and the case is vacuous. -/
theorem isolatedComponentBound_of_sideZeroBase (D : RelGenSet G Λ)
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
    ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D mu b n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (15 * C * n) := by
  intro n hn6 v u hpoly nu i k hcomp hiso
  obtain ⟨hlet, hclosed, c, hc0, hcn, hcmono, hcqg⟩ := hpoly
  have hik : i < k := hcomp.1
  have hku : k ≤ u.length := hcomp.2.1
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd hcn (by omega)
    · exact hpos
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  obtain ⟨t, ht, hti, hit⟩ := exists_side_of_index c hc0 n i hn1 (by omega)
  obtain ⟨t', ht', htk, hkt'⟩ := exists_side_of_index c hc0 n k hn1 (by omega)
  have htt' : t ≤ t' := by
    by_contra hcon
    have h : c (t' + 1) ≤ c t := hmono (by omega)
    omega
  exact isolatedComponent_span_of_sideZeroBase D hsymm mu b hmu hb C hbase hn6
    ht hti hit ht' htk hkt' htt' hlet hclosed hc0 hcn hcmono hcqg hcomp hiso

/-! ## The bound, with nothing left assumed -/

/-- **Dahmani--Guirardel--Osin's isolated-component bound for polygons of at most
six sides, from four-point hyperbolicity alone.**

`DGOIsolatedComponentBoundFourGon.span_mem_relBall_of_sideZero` is their Lemma
4.16 at four sides, with `C = 25 (δ + b + 1)`; `baseCase_of_sideZero_at` puts it
in the binder shape, and everything above turns it into the bound for an
arbitrary isolated component of a `(1,b)`-quasi-geodesic `n`-gon, `n ≤ 6`.

No hypothesis remains but the two the base case itself carries: a base closed
under inversion, and `Γ(G, X ⊔ ℋ)` four-point hyperbolic.  The `b` enters only
through their thinness constant `12δ + 2b`; nothing between the base case and
here reads it, which is why the chain above is stated at a free `(mu, b)`. -/
theorem isolatedComponentBound_of_fourPointHyperbolic_at (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 (b : ℝ) n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k
          ∈ D.relBall nu (15 * (25 * (δ + b + 1)) * n) :=
  isolatedComponentBound_of_sideZeroBase D hsymm 1 (b : ℝ) le_rfl
    (Nat.cast_nonneg b) (25 * (δ + b + 1))
    (baseCase_of_sideZero_at D hsymm hδ (b := b) rfl)

/-- **The geodesic case**, `b = 0`: the shape the geodesic-polygon applications
use.  Only the cast `((0 : ℕ) : ℝ) = 0` separates it from the statement
above. -/
theorem isolatedComponentBound_of_fourPointHyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k
          ∈ D.relBall nu (15 * (25 * (δ + 1)) * n) := by
  intro n hn6 v u hpoly nu i k hcomp hiso
  have hpoly' : IsQuasiGeodesicPolygon D 1 ((0 : ℕ) : ℝ) n v u := by
    rwa [Nat.cast_zero]
  have h := isolatedComponentBound_of_fourPointHyperbolic_at D hsymm 0 hδ n hn6
    v u hpoly' nu i k hcomp hiso
  rwa [show δ + 0 + 1 = δ + 1 from by omega] at h

end OsinComponents
end GGT
end GroupApproximation
