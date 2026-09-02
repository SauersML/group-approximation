import GroupApproximation.GGT.DGOProposition414Uniform

/-!
# The quasi-geodesic parameter conversion for Proposition 4.14

The balanced-surgery chain supplies `SumBound D b n K`, whose side inequality
is `(q-p)-b ≤ d`.  Lemma 4.20 supplies arbitrary `(μ,c)`-quasi-geodesic
sides.  This file isolates the missing arithmetic comparison between those
two inequalities and proves the radius-witness conversion from that smaller
input.  The comparison is the single geometric estimate still needed before
the exact `DGOUniformSumBound` interface can be connected without importing the
proof-layer module that defines it.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414
namespace General

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The arithmetic comparison needed to replace a `(μ,c)` side inequality by
the `(1,b)` inequality used by the balanced-surgery `SumBound`. -/
def QuasiGeodesicComparison (mu c b : ℝ) : Prop :=
  ∀ (_hmu : 1 ≤ mu) (_hc : 0 ≤ c) (t d : ℝ),
    0 ≤ t → 0 ≤ d → t / mu - c ≤ d → t - b ≤ d

/-- The one-point arithmetic model satisfies the comparison at `(μ,c,b)=(1,0,0)`. -/
theorem quasiGeodesicComparison_zeroModel :
    QuasiGeodesicComparison 1 0 0 := by
  intro hmu hc t d ht hd h
  norm_num at hmu hc h ⊢
  exact h

/-- A zero-side polygon contributes no distinguished radius. -/
theorem zeroSideRadiusWitness
    (D : RelGenSet G Λ) (_mu _c : ℝ) (n : ℕ)
    (hzero : n = 0) (v : G) (word : List (RelLetter G Λ))
    (cut : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ)
    (hI : ∀ s ∈ I, s < n) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) ∈
          D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ 0 := by
  subst n
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro s hs
    have hs0 := hI s hs
    omega
  · simp

/-- A linear family of fixed-parameter `SumBound`s gives the radius-witness
bound for `(μ,c)`-quasi-geodesic sides whenever
`QuasiGeodesicComparison μ c b` is available. -/
theorem exists_general_radius_bound_of_linearSumBound
    (D : RelGenSet G Λ) (b : ℕ)
    (hlin : ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n →
      SumBound D (b : ℝ) n (L * n))
    (mu c : ℝ) (hmu : 1 ≤ mu) (hc : 0 ≤ c)
    (hcompare : QuasiGeodesicComparison mu c (b : ℝ)) :
    ∃ C : ℕ, 0 < C ∧
      (∀ (n : ℕ) (v : G) (word : List (RelLetter G Λ))
          (cut : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ),
        (∀ a ∈ word, D.IsLetter a) →
        RelLetter.listVal word = 1 →
        IsPolygonCut n word cut →
        (∀ s ∈ I, s < n) →
        (∀ s ∈ I, cut (s + 1) = cut s + 1) →
        (∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1))) →
        (∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s)) →
        (∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
          cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
          ((q - p : ℕ) : ℝ) / mu - c ≤
            ((wordDist D.alphabet.carrier
              (vertex v word p) (vertex v word q) : ℕ) : ℝ)) →
        ∃ r : ℕ → ℕ,
          (∀ s ∈ I,
            (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) ∈
              D.relBall (lam s) (r s)) ∧
          ∑ s ∈ I, r s ≤ C * n) := by
  obtain ⟨L, hL⟩ := hlin
  refine ⟨L + 1, Nat.zero_lt_succ L, ?_⟩
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  by_cases hn : n = 0
  · subst n
    obtain ⟨r, hr, hsum⟩ := zeroSideRadiusWitness D mu c 0 rfl v word cut I lam hI
    refine ⟨r, hr, ?_⟩
    simpa using hsum
  · have hnpos : 1 ≤ n := by omega
    have hsum := hL n hnpos
    have hquasiOne : ∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
        cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
        ((q - p : ℕ) : ℝ) - (b : ℝ) ≤
          ((wordDist D.alphabet.carrier
            (vertex v word p) (vertex v word q) : ℕ) : ℝ) := by
      intro s hs hnot p q hp hpq hq
      have hqgeneral := hquasi s hs hnot p q hp hpq hq
      have ht : 0 ≤ ((q - p : ℕ) : ℝ) := by positivity
      have hd : 0 ≤
          ((wordDist D.alphabet.carrier
            (vertex v word p) (vertex v word q) : ℕ) : ℝ) := by
        positivity
      exact hcompare hmu hc ((q - p : ℕ) : ℝ)
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ)
        ht hd hqgeneral
    obtain ⟨r, hr, htotal⟩ := hsum v word cut I lam hlet hclosed hcut hI
      hedge hcomp hiso hquasiOne
    refine ⟨r, hr, ?_⟩
    have hsucc : L * n ≤ (L + 1) * n := by
      exact Nat.mul_le_mul_right n (by omega)
    exact le_trans htotal hsucc

end General
end DGOProposition414
end GGT
end GroupApproximation
