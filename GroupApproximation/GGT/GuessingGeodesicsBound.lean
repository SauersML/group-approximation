import GroupApproximation.GGT.GuessingGeodesicsGrowth
import GroupApproximation.GGT.GuessingGeodesicsSubdivision

/-!
# The bound function of Bowditch's criterion

The subdivision bound of `GGT/GuessingGeodesicsSubdivision.lean` is uniform on
each ball but grows with the ball: at scale `n` it is `(t + 1) * K` for any `t`
with `n ≤ 2 ^ t`.  Bowditch's bootstrap removes that growth by feeding the bound
back into itself, and to state the recursion at all one needs the bound as a
*function* of the scale.

This module supplies it.  `Bnd D n b` says that `b` works at scale `n`, and
`pathBound D n` is the least such `b`, taken as `sInf` --- exactly as
`Algebra/WordMetric.lean` defines `wordNorm`, and for the same reason: `Bnd`
quantifies over group elements, so it is not decidable and `Nat.find` is not
available.

## Two design points

**`Bnd` quantifies over every geodesic chain, not some chain.**  The bootstrap
cuts a geodesic into three sub-chains and applies the bound to each of them, so
a formulation promising only one geodesic would break at that step.  Nothing is
lost: `exists_chain_index_close` already proves the `∀`-form.

**The chain lemmas come first.**  Those three sub-chains are a restriction and
two shifts of one chain, so `IsGeodesicChain.mono` and `IsGeodesicChain.shift`
are what makes the cut expressible; they are stated here because
`IsGeodesicChain` had neither.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## Restricting and shifting a geodesic chain -/

/-- **A geodesic chain restricts.**  The condition says nothing past its
length, so shortening it is free. -/
theorem IsGeodesicChain.mono {S : Set G} {c : ℕ → G} {n m : ℕ}
    (h : IsGeodesicChain S c n) (hm : m ≤ n) : IsGeodesicChain S c m :=
  fun i j hij hjm => h i j hij (le_trans hjm hm)

/-- **A geodesic chain shifts.**  Reading it from index `a` gives a geodesic
chain of length `n - a`, which is the sub-chain a cut of the geodesic at `a`
produces. -/
theorem IsGeodesicChain.shift {S : Set G} {c : ℕ → G} {n a : ℕ}
    (h : IsGeodesicChain S c n) (ha : a ≤ n) :
    IsGeodesicChain S (fun i => c (a + i)) (n - a) := by
  intro i j hij hjn
  show wordDist S (c (a + i)) (c (a + j)) = j - i
  rw [h (a + i) (a + j) (by omega) (by omega)]
  omega

namespace OsinEnlargement

/-! ## The predicate and the function -/

/-- **`b` is a bound at scale `n`**: for every pair at distance at most `n`,
every vertex of the path joining them is within `b` of **every** geodesic
chain joining them. -/
def Bnd {S : Set G} {K : ℕ} (D : GuessingData S K) (n b : ℕ) : Prop :=
  ∀ x y : G, wordDist S x y ≤ n → ∀ c : ℕ → G, c 0 = x →
    c (wordDist S x y) = y → IsGeodesicChain S c (wordDist S x y) →
      ∀ i ≤ D.len x y, ∃ k ≤ wordDist S x y,
        wordDist S (D.path x y i) (c k) ≤ b

/-- A bound only weakens as the constant grows. -/
theorem Bnd.mono {S : Set G} {K : ℕ} {D : GuessingData S K} {n b b' : ℕ}
    (h : Bnd D n b) (hb : b ≤ b') : Bnd D n b' := by
  intro x y hxy c hc0 hcn hchain i hi
  obtain ⟨k, hk, hkd⟩ := h x y hxy c hc0 hcn hchain i hi
  exact ⟨k, hk, le_trans hkd hb⟩

/-- **The subdivision bound, as a bound at a scale.** -/
theorem bnd_of_pow {S : Set G} (hS : IsSymmetricGeneratingSet S) {K : ℕ}
    (D : GuessingData S K) {n t : ℕ} (hn : n ≤ 2 ^ t) :
    Bnd D n ((t + 1) * K) := by
  intro x y hxy c hc0 hcn hchain i hi
  have hi' : i ≤ D.len (c 0) (c (wordDist S x y)) := by
    rw [hc0, hcn]
    exact hi
  obtain ⟨k, -, hkn, hkd⟩ := exists_chain_index_close hS D hchain t 0
    (wordDist S x y) (Nat.zero_le _) le_rfl (by omega) i hi'
  rw [hc0, hcn] at hkd
  exact ⟨k, hkn, hkd⟩

/-- Some bound holds at every scale, so the infimum below is over a nonempty
set: take the exponent to be the scale itself, `n + 1 ≤ 2 ^ n`. -/
theorem nonempty_setOf_bnd {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) (n : ℕ) :
    {b : ℕ | Bnd D n b}.Nonempty := by
  refine ⟨(n + 1) * K, ?_⟩
  show Bnd D n ((n + 1) * K)
  have h := succ_le_two_pow n
  exact bnd_of_pow hS D (by omega)

/-- **The least bound at scale `n`.**

`sInf` rather than `Nat.find`, `Bnd` being a statement about group elements and
so not decidable; this is the definition `WordMetric.wordNorm` already uses. -/
noncomputable def pathBound {S : Set G} {K : ℕ} (D : GuessingData S K)
    (n : ℕ) : ℕ :=
  sInf {b : ℕ | Bnd D n b}

/-- The least bound is a bound. -/
theorem bnd_pathBound {S : Set G} (hS : IsSymmetricGeneratingSet S) {K : ℕ}
    (D : GuessingData S K) (n : ℕ) : Bnd D n (pathBound D n) :=
  Nat.sInf_mem (nonempty_setOf_bnd hS D n)

/-- It is least. -/
theorem pathBound_le {S : Set G} {K : ℕ} {D : GuessingData S K} {n b : ℕ}
    (h : Bnd D n b) : pathBound D n ≤ b :=
  Nat.sInf_le h

/-- **The subdivision bound, read on `pathBound`.**  This is the only input the
bootstrap takes from the geometry of `GGT/GuessingGeodesicsSubdivision.lean`. -/
theorem pathBound_le_of_pow {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) {n t : ℕ} (hn : n ≤ 2 ^ t) :
    pathBound D n ≤ (t + 1) * K :=
  pathBound_le (bnd_of_pow hS D hn)

end OsinEnlargement
end GGT
end GroupApproximation
