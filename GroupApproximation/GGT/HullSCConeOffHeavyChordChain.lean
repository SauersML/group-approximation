import GroupApproximation.Algebra.MorseLemma
import GroupApproximation.GGT.MorseLemmaDischarge

/-!
# The other half of the Morse lemma: a chord point near the chain

`Hyperbolic.MorseLemma` (`Algebra/MorseLemma.lean`) is stated in the *chain near
chord* direction: every vertex of a quasi-geodesic is within `R` of a point
lying between the endpoints.  Quasiconvexity — which is what
`GGT/HullSCConeOffHeavyHyperbolic.lean` needs, and through
`GGT.OsinEnlargement.osinLemma55` the whole hyperbolicity clause of the cone-off
— is the *chord near chain* direction: every point between the endpoints is
close to a vertex.

This module derives the second from the first, so that the cone-off's clause (a)
rests on exactly one named statement and not on two.

## The derivation

Let `q m` be the between-point the Morse lemma supplies for the vertex `p m`,
and let `t m = d(p 0, q m)` be its parameter along the chord.  Three
observations finish it.

* Consecutive parameters are close: `t (m+1) ≤ t m + (2R + K + C)`, by going
  `q m → p m → p (m+1) → q (m+1)` and using the quasi-geodesic's upper bound on
  the middle step.
* `t 0 ≤ R` and the last parameter is within `R` of the whole chord length, so
  the parameters are `(2R + K + C)`-dense in `[0, d(p 0, p n)]`.  That is
  `exists_index_param_close`, an induction on `n` with no geometry in it: at
  each step either the target is already below `t n`, in which case the
  induction hypothesis applies, or it is not, in which case `n` itself is the
  index.
* Two points between the same endpoints whose parameters differ by at most `s`
  are `s + 2δ` apart.  That is `wordDist_le_of_isBetween_of_param_le`, one
  application of the four-point condition, and it is the `≤` generalisation of
  the landed `GGT.wordDist_le_two_mul_of_isBetween`, which is its `=` case.

The constant that comes out is `4R + K + C + 2δ`.

## Scope

`Hyperbolic.morseLemma_univ` states the Morse lemma at `Type u`, so the
statement below is now at `Type u` too and nothing here is confined to universe
zero.  The `..._of_morse` form is kept as its `Type 0` instance so that no caller
moves; its hypothesis is redundant and is named `_hmorse` for that reason.

The two auxiliary lemmas are general facts about betweenness and about natural
numbers, and have nothing to do with cone-offs; they are here rather than in
`Algebra/` only because this lane owns the `HullSCConeOffHeavy*` prefix.  If the
lane that owns `Algebra/HyperbolicSlimTriangles.lean` wants them, they should
move.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## Two between-points with close parameters -/

/-- **Between-points whose parameters differ by at most `s` are `s + 2δ`
apart.**

One application of the four-point condition at `(x, z, p, q)`.  Both competing
pairings are at most `d(x,z) + s`: the first is
`d(x,p) + d(q,z) = d(x,z) + (d(x,p) - d(x,q))` and the second is its mirror, so
each is controlled by one of the two hypotheses.  What is left over for
`d(p,q)` is `s + 2δ`.

At `s = 0` this is `GGT.wordDist_le_two_mul_of_isBetween`. -/
theorem wordDist_le_of_isBetween_of_param_le {G : Type u} [Group G] {S : Set G}
    {delta s : ℕ} (hS : IsSymmetricGeneratingSet S)
    (hdelta : Hyperbolic.IsFourPointHyperbolic S delta) {x z p q : G}
    (hp : Hyperbolic.IsBetween S x p z) (hq : Hyperbolic.IsBetween S x q z)
    (h1 : wordDist S x p ≤ wordDist S x q + s)
    (h2 : wordDist S x q ≤ wordDist S x p + s) :
    wordDist S p q ≤ s + 2 * delta := by
  have h := hdelta x z p q
  have hb1 : wordDist S x p + wordDist S p z = wordDist S x z := hp
  have hb2 : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have hzp : wordDist S z p = wordDist S p z := wordDist_comm hS z p
  have hzq : wordDist S z q = wordDist S q z := wordDist_comm hS z q
  omega

/-! ## Density of a slowly moving sequence -/

/-- **A sequence of naturals that starts low and moves slowly is dense up to its
last value.**

If `t 0 ≤ rad`, consecutive terms differ upward by at most `step`, and
`x ≤ t n + rad`, then some index has `t m` within `step + rad` of `x` on one
side and `rad` on the other.

The induction is on `n` and carries no geometry: either `x ≤ t n + rad` already
holds one step down, and the induction hypothesis applies, or it does not, and
`n` itself is the index — below `x` by the failed case hypothesis, and above
`x - (step + rad)` because one step of the sequence covers the gap. -/
theorem exists_index_param_close (t : ℕ → ℕ) (step rad : ℕ) :
    ∀ (n x : ℕ), (∀ m, m < n → t (m + 1) ≤ t m + step) → t 0 ≤ rad →
      x ≤ t n + rad →
        ∃ m ≤ n, t m ≤ x + rad ∧ x ≤ t m + (step + rad) := by
  intro n
  induction n with
  | zero =>
      intro x _hstep h0 hxn
      exact ⟨0, le_refl 0, by omega, by omega⟩
  | succ n ih =>
      intro x hstep h0 hxn
      by_cases hcase : x ≤ t n + rad
      · obtain ⟨m, hmn, h1, h2⟩ :=
          ih x (fun m hm => hstep m (by omega)) h0 hcase
        exact ⟨m, by omega, h1, h2⟩
      · refine ⟨n, Nat.le_succ n, by omega, ?_⟩
        have hs := hstep n (by omega)
        omega

/-! ## Chord near chain -/

/-- **Every point between the endpoints of a quasi-geodesic is near one of its
vertices**, with a constant depending only on `K`, `C` and `δ`.

This is the direction `Hyperbolic.MorseLemma` does not state, derived from the
one it does.  See the module header for the three steps and for the constant
`4R + K + C + 2δ`. -/
theorem exists_index_wordDist_le_of_isBetween_of_fourPoint (K C delta : ℕ) :
    ∃ R : ℕ, ∀ (G : Type u) (_hG : Group G) (S : Set G),
      IsSymmetricGeneratingSet S → Hyperbolic.IsFourPointHyperbolic S delta →
        ∀ (n : ℕ) (p : ℕ → G), Hyperbolic.IsQuasiGeodesic S K C n p →
          ∀ z : G, Hyperbolic.IsBetween S (p 0) z (p n) →
            ∃ m ≤ n, wordDist S (p m) z ≤ R := by
  obtain ⟨R, hR⟩ := Hyperbolic.morseLemma_univ K C delta
  refine ⟨4 * R + K + C + 2 * delta, ?_⟩
  intro G _hG S hS hdelta n p hp z hz
  have hqex : ∀ m : ℕ, ∃ q : G, Hyperbolic.IsBetween S (p 0) q (p n) ∧
      (m ≤ n → wordDist S (p m) q ≤ R) := by
    intro m
    by_cases hm : m ≤ n
    · obtain ⟨q, hq1, hq2⟩ := hR G _hG S hS hdelta n p hp m hm
      exact ⟨q, hq1, fun _ => hq2⟩
    · exact ⟨p 0, Hyperbolic.isBetween_left S (p 0) (p n), fun h => absurd h hm⟩
  choose q hq1 hq2 using hqex
  have hstep : ∀ m, m < n →
      wordDist S (p 0) (q (m + 1))
        ≤ wordDist S (p 0) (q m) + (2 * R + K * 1 + C) := by
    intro m hm
    have hpm := (hp m (by omega) (m + 1) (by omega) (by omega)).1
    have hsub : m + 1 - m = 1 := by omega
    rw [hsub] at hpm
    have h1 := hq2 m (by omega)
    have h2 := hq2 (m + 1) (by omega)
    have t1 := wordDist_triangle hS (p 0) (q m) (q (m + 1))
    have t2 := wordDist_triangle hS (q m) (p m) (q (m + 1))
    have t3 := wordDist_triangle hS (p m) (p (m + 1)) (q (m + 1))
    have c1 := wordDist_comm hS (q m) (p m)
    omega
  have h0 : wordDist S (p 0) (q 0) ≤ R := hq2 0 (Nat.zero_le n)
  have hlast : wordDist S (p 0) z ≤ wordDist S (p 0) (q n) + R := by
    have hbz : wordDist S (p 0) z + wordDist S z (p n)
        = wordDist S (p 0) (p n) := hz
    have htri := wordDist_triangle hS (p 0) (q n) (p n)
    have hqn := hq2 n (le_refl n)
    have hc := wordDist_comm hS (q n) (p n)
    omega
  obtain ⟨m, hmn, hle1, hle2⟩ :=
    exists_index_param_close (fun i => wordDist S (p 0) (q i))
      (2 * R + K * 1 + C) R n (wordDist S (p 0) z) hstep h0 hlast
  have hs1 : wordDist S (p 0) z ≤ wordDist S (p 0) (q m) + (3 * R + K + C) := by
    have : K * 1 = K := by omega
    omega
  have hs2 : wordDist S (p 0) (q m) ≤ wordDist S (p 0) z + (3 * R + K + C) := by
    omega
  have hzq := wordDist_le_of_isBetween_of_param_le hS hdelta hz (hq1 m) hs1 hs2
  refine ⟨m, hmn, ?_⟩
  have htri := wordDist_triangle hS (p m) (q m) z
  have hpm := hq2 m hmn
  have hc := wordDist_comm hS (q m) z
  omega

/-- **The Morse-conditional form**, kept so that no caller moves.

Its statement is unchanged and its hypothesis is now redundant --- discharged by
`Hyperbolic.morseLemma_univ` in the theorem above, of which this is the `Type 0`
instance.  Callers pass the hypothesis positionally and are unaffected. -/
theorem exists_index_wordDist_le_of_isBetween_of_morse
    (_hmorse : Hyperbolic.MorseLemma) (K C delta : ℕ) :
    ∃ R : ℕ, ∀ (G : Type) (_hG : Group G) (S : Set G),
      IsSymmetricGeneratingSet S → Hyperbolic.IsFourPointHyperbolic S delta →
        ∀ (n : ℕ) (p : ℕ → G), Hyperbolic.IsQuasiGeodesic S K C n p →
          ∀ z : G, Hyperbolic.IsBetween S (p 0) z (p n) →
            ∃ m ≤ n, wordDist S (p m) z ≤ R :=
  exists_index_wordDist_le_of_isBetween_of_fourPoint K C delta

end HullSC
end GroupApproximation
