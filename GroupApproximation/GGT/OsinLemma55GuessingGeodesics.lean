import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.OsinTheorem54SepLemma55

/-!
# Osin's Lemma 5.5 from Bowditch's guessing-geodesics criterion

`GGT/OsinTheorem54SepLemma55.lean` declares `OsinLemma55` as a debt and records
what is known about it.  This module discharges everything about that debt
except one standard criterion, which is declared here in its place.

## The chain of attributions

Osin states his Lemma 5.5 as *"([32, Corollary 2.4])"* with no proof, [32] being
Kapovich--Rafi, *On hyperbolicity of free splitting and free factor complexes*,
and remarks that he states it in a much simplified form --- in Kapovich--Rafi's
notation `L = M₁ = 1` and `M₂ = M`.  Kapovich--Rafi's Corollary 2.4 is in turn an
application of Bowditch's criterion, which is the statement declared below.  So
the derivation chain is

    Bowditch's criterion  ⟹  Kapovich--Rafi, Cor 2.4  ⟹  Osin, Lemma 5.5 ,

and what this module proves is the last arrow, unconditionally.  Only the first
statement is assumed.  (An earlier docstring in this tree attributed Lemma 5.5 to
Breuillard--Cornulier; that was this repository's error, not the literature's,
and it is corrected at `GGT/OsinSeparatingCosets.lean`.)

## Why a criterion is needed at all

The naive route --- transport the four-point inequality from the old alphabet to
the new with a bounded error --- is refuted in the debt module: at `A = {t^±1}`
and `B = ℤ` the Gromov product `(t^n | t^{2n})_1` is `n` on one side and `1/2` on
the other while `M` stays at one.  The whole point of an enlargement is that
`d_B` is much *smaller* than `d_A`, so the two metrics are nowhere near bounded
distance, and no perturbation argument survives.

What does survive is a criterion that never compares the two metrics: one
supplies, for each pair of points of the *new* graph, a connected path, and
checks two conditions on that family.  Here the path is an *old* geodesic, and
the two conditions are exactly the hypothesis of Lemma 5.5 and the slimness of
the old triangles.

## The two conditions, and the constants

With `γ x y` the chain along an `A`-geodesic word from `x` to `y`:

* **Short pairs.**  If `d_B(x,y) ≤ 1` then `x⁻¹y` is a `B`-letter (or `1`), and
  the hypothesis of Lemma 5.5 puts every vertex of `γ x y` within `d_B ≤ M` of
  `x`; so the chain has `d_B`-diameter at most `2M`.
* **Triangles.**  A vertex of `γ x y` lies between `x` and `y` in the `A`-metric,
  so `A`-slimness --- `Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic` at
  `4⌈δ⌉₊` --- puts it `A`-within `4⌈δ⌉₊` of a point between `x` and `z` or
  between `z` and `y`.  That point need not lie on the *chosen* chain, and the
  gap costs `2⌈δ⌉₊` more: two points between `x` and `z` at the same distance
  from `x` are `2δ` apart, which is the four-point condition at `(q,c,x,z)`,
  where both pairings equal `d(x,z)`.  Finally `d_B ≤ d_A`.

So the criterion applies at `K = max (2M) (6⌈δ⌉₊)`, and its conclusion converts
back through `CayleyFourPointBridge.isHyperbolicSpace_cayley_of_fourPoint`.

## What `M` is downstream

Osin's Lemma 5.6 instantiates the diameter bound at `M = 2`: for `y ∈ Y` every
vertex of an `X`-geodesic from `1` to `y` is itself in `Y`, the condition
`S(1,·;D) = ∅` being inherited by subgeodesics.  Nothing here depends on that;
it is recorded so that the constant is not mistaken for a free parameter.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

/-! ## The criterion -/

/-- **Bowditch's guessing-geodesics criterion**, in the chain vocabulary this
repository states hyperbolicity in.

Suppose that for every pair of points of `Γ(G,S)` one is given a path `γ x y`
from `x` to `y` --- a chain of vertices, consecutive ones at distance at most one
--- such that

* the path joining two points at distance at most one has diameter at most `K`;
* every vertex of `γ x y` is within `K` of a vertex of `γ x z` or of `γ z y`.

Then `Γ(G,S)` satisfies the four-point condition, at a constant depending only
on `K`.

The paths are **not** assumed to be quasi-geodesics, and that is the whole
strength of the criterion: in the application below they are geodesics of a
*different*, much longer metric, and the image of one in `Γ(G,S)` can have
length unboundedly larger than its diameter.

Proved, in `GGT/GuessingGeodesicsCriterion.lean`, by a dyadic subdivision
followed by a bootstrap removing the resulting logarithm.  It is stated here as
a named `Prop` because this module was written before that proof existed; the
reduction below is unchanged, and `OsinEnlargement.osinLemma55` reads it as a
theorem. -/
def GuessingGeodesics : Prop :=
  ∀ (H : Type u) [Group H] (S : Set H), IsSymmetricGeneratingSet S →
    ∀ (K : ℕ) (len : H → H → ℕ) (γ : H → H → ℕ → H),
      (∀ x y : H, γ x y 0 = x) →
      (∀ x y : H, γ x y (len x y) = y) →
      (∀ (x y : H) (i : ℕ), i < len x y →
        wordDist S (γ x y i) (γ x y (i + 1)) ≤ 1) →
      (∀ x y : H, wordDist S x y ≤ 1 → ∀ i ≤ len x y, ∀ j ≤ len x y,
        wordDist S (γ x y i) (γ x y j) ≤ K) →
      (∀ x y z : H, ∀ i ≤ len x y, ∃ j : ℕ,
        (j ≤ len x z ∧ wordDist S (γ x y i) (γ x z j) ≤ K) ∨
        (j ≤ len z y ∧ wordDist S (γ x y i) (γ z y j) ≤ K)) →
      ∃ δ : ℕ, Hyperbolic.IsFourPointHyperbolic S δ

/-! ## Two geodesics with the same endpoints -/

/-- **Two points between the same pair, at the same distance from one end, are
`2δ` apart.**

The four-point condition at `(q,c,x,z)`: both alternative pairings come to
`d(x,z)`, one as `d(x,q) + d(c,z)` and the other as `d(q,z) + d(x,c)`, so the
maximum is `d(x,z)` and the inequality reads `d(q,c) ≤ 2δ`.

This is what replaces "two geodesics with common endpoints fellow-travel" in a
vocabulary where geodesics are not objects. -/
theorem wordDist_le_of_isBetween_of_wordDist_eq {G : Type u} [Group G]
    {S : Set G} (hS : IsSymmetricGeneratingSet S) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ) {x z q c : G}
    (hq : Hyperbolic.IsBetween S x q z) (hc : Hyperbolic.IsBetween S x c z)
    (heq : wordDist S x q = wordDist S x c) :
    wordDist S q c ≤ 2 * δ := by
  have hkey := hδ q c x z
  have hqx : wordDist S q x = wordDist S x q := wordDist_comm hS q x
  have hcx : wordDist S c x = wordDist S x c := wordDist_comm hS c x
  have hq' : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have hc' : wordDist S x c + wordDist S c z = wordDist S x z := hc
  have h1 : wordDist S q x + wordDist S c z = wordDist S x z := by omega
  have h2 : wordDist S q z + wordDist S c x = wordDist S x z := by omega
  rw [h1, h2, max_self] at hkey
  omega

/-! ## Lemma 5.5 from the criterion -/

/-- **Osin's Lemma 5.5 holds if Bowditch's criterion does.**

The chain supplied to the criterion is the vertex sequence of a geodesic word of
the *old* alphabet, chosen once for each pair.  See the module header for the
two conditions and the constants; `K = max (2M) (6⌈δ⌉₊)`.

The bridges at both ends are already theorems of this tree:
`CayleyFourPointConverse.isFourPointHyperbolic_of_isHyperbolicSpace_cayley` going
in and `CayleyFourPointBridge.isHyperbolicSpace_cayley_of_fourPoint` coming out,
so the argument runs entirely in `IsBetween` and `wordDist` and never needs a
metric-space structure on the Cayley graph. -/
theorem osinLemma55_of_guessingGeodesics (hgg : GuessingGeodesics.{u}) :
    OsinLemma55.{u} := by
  intro G _ A B hAB δ hδ M hMcond
  have hSA : IsSymmetricGeneratingSet A.carrier := A.symmetricGenerating
  have hSB : IsSymmetricGeneratingSet B.carrier := B.symmetricGenerating
  have hfour : Hyperbolic.IsFourPointHyperbolic A.carrier ⌈δ⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley A hδ
  have hslim : Hyperbolic.IsSlimTriangles A.carrier (4 * ⌈δ⌉₊) :=
    Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hSA hfour
  have hmono : ∀ x y : G, wordDist B.carrier x y ≤ wordDist A.carrier x y :=
    fun x y => wordNorm_mono hAB (wordLengths_nonempty hSA _)
  -- one geodesic word of the old alphabet for each pair
  have hgw : ∀ x y : G, ∃ l : List G, IsGeodesicWord A.carrier l (x⁻¹ * y) :=
    fun x y => exists_isGeodesicWord hSA (x⁻¹ * y)
  choose word hword using hgw
  -- its vertices march out at unit speed and lie between the endpoints
  have hbet : ∀ (a c : G) (n : ℕ), n ≤ (word a c).length →
      Hyperbolic.IsBetween A.carrier a (a * ((word a c).take n).prod) c ∧
        wordDist A.carrier a (a * ((word a c).take n).prod) = n := by
    intro a c n hn
    have hsplit : (word a c).take n ++ (word a c).drop n = word a c :=
      List.take_append_drop n (word a c)
    have hgeo : IsGeodesicWord A.carrier
        ((word a c).take n ++ (word a c).drop n)
        (((word a c).take n ++ (word a c).drop n)).prod := by
      rw [hsplit]
      refine ⟨⟨(hword a c).isWord.letters, rfl⟩, ?_⟩
      rw [(hword a c).isWord.prod_eq]
      exact (hword a c).length_eq
    obtain ⟨hb, hd⟩ := Hyperbolic.isBetween_of_geodesic_append hSA a hgeo
    rw [hsplit, (hword a c).isWord.prod_eq, mul_inv_cancel_left] at hb
    refine ⟨hb, ?_⟩
    rw [hd]
    exact Hyperbolic.length_take_of_le hn
  -- clause one: the chain starts at `x`
  have hzero : ∀ x y : G, x * ((word x y).take 0).prod = x := by
    intro x y
    rw [List.take_zero, List.prod_nil, mul_one]
  -- clause two: and ends at `y`
  have hlast : ∀ x y : G,
      x * ((word x y).take (word x y).length).prod = y := by
    intro x y
    rw [List.take_length, (hword x y).isWord.prod_eq, mul_inv_cancel_left]
  -- clause three: consecutive vertices are one letter apart, in either alphabet
  have hstep : ∀ (x y : G) (i : ℕ), i < (word x y).length →
      wordDist B.carrier (x * ((word x y).take i).prod)
        (x * ((word x y).take (i + 1)).prod) ≤ 1 := by
    intro x y i hi
    rw [List.prod_take_succ (word x y) i hi]
    have hval : wordDist B.carrier (x * ((word x y).take i).prod)
        (x * (((word x y).take i).prod * (word x y)[i]'hi))
        = wordNorm B.carrier ((word x y)[i]'hi) := by
      show wordNorm B.carrier ((x * ((word x y).take i).prod)⁻¹ *
        (x * (((word x y).take i).prod * (word x y)[i]'hi))) = _
      congr 1
      group
    rw [hval]
    exact wordNorm_le_one_of_mem
      (hAB ((hword x y).isWord.letters _ (List.getElem_mem hi)))
  -- clause four: the chain of a short pair has diameter at most `2M`
  have hclose : ∀ x y : G, wordDist B.carrier x y ≤ 1 →
      ∀ i ≤ (word x y).length, ∀ j ≤ (word x y).length,
        wordDist B.carrier (x * ((word x y).take i).prod)
            (x * ((word x y).take j).prod)
          ≤ max (2 * M) (6 * ⌈δ⌉₊) := by
    intro x y hxy i hi j hj
    have hxy' : wordNorm B.carrier (x⁻¹ * y) ≤ 1 := hxy
    obtain ⟨l, hl, hllen⟩ := exists_isWord_length_eq hSB (x⁻¹ * y)
    rcases l with _ | ⟨a, t⟩
    · have hone : x⁻¹ * y = 1 := by
        have hp := hl.prod_eq
        rw [List.prod_nil] at hp
        exact hp.symm
      have hlen0 : (word x y).length = 0 := by
        rw [(hword x y).length_eq, hone, wordNorm_one]
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0
      subst hj0
      rw [List.take_zero, List.prod_nil, mul_one, wordDist_self]
      exact Nat.zero_le _
    · have hlent : t.length = 0 := by
        rw [List.length_cons] at hllen
        omega
      have hnil : t = [] := List.eq_nil_of_length_eq_zero hlent
      have hprod : x⁻¹ * y = a := by
        have hp := hl.prod_eq
        rw [hnil, List.prod_cons, List.prod_nil, mul_one] at hp
        exact hp.symm
      have hbmem : x⁻¹ * y ∈ B.carrier := by
        rw [hprod]
        exact hl.letters a List.mem_cons_self
      have hwlen : (word x y).length = wordDist A.carrier 1 (x⁻¹ * y) := by
        rw [wordDist_one_left]
        exact (hword x y).length_eq
      have hMi := hMcond (x⁻¹ * y) hbmem (word x y) (hword x y).isWord.letters
        (hword x y).isWord.prod_eq hwlen i hi
      have hMj := hMcond (x⁻¹ * y) hbmem (word x y) (hword x y).isWord.letters
        (hword x y).isWord.prod_eq hwlen j hj
      have hleft : wordDist B.carrier (x * ((word x y).take i).prod)
          (x * ((word x y).take j).prod)
          = wordDist B.carrier (((word x y).take i).prod)
            (((word x y).take j).prod) :=
        wordDist_left_invariant B.carrier x _ _
      have htri := wordDist_triangle hSB (((word x y).take i).prod) 1
        (((word x y).take j).prod)
      have hcomm : wordDist B.carrier (((word x y).take i).prod) 1
          = wordDist B.carrier 1 (((word x y).take i).prod) :=
        wordDist_comm hSB _ _
      have hfin : wordDist B.carrier (x * ((word x y).take i).prod)
          (x * ((word x y).take j).prod) ≤ 2 * M := by omega
      exact le_trans hfin (le_max_left (2 * M) (6 * ⌈δ⌉₊))
  -- clause five: old slimness, read in the new metric
  have hthin : ∀ x y z : G, ∀ i ≤ (word x y).length, ∃ j : ℕ,
      (j ≤ (word x z).length ∧
          wordDist B.carrier (x * ((word x y).take i).prod)
            (x * ((word x z).take j).prod) ≤ max (2 * M) (6 * ⌈δ⌉₊)) ∨
        (j ≤ (word z y).length ∧
          wordDist B.carrier (x * ((word x y).take i).prod)
            (z * ((word z y).take j).prod) ≤ max (2 * M) (6 * ⌈δ⌉₊)) := by
    intro x y z i hi
    obtain ⟨hbetp, -⟩ := hbet x y i hi
    rcases hslim x y z (x * ((word x y).take i).prod) hbetp with
      ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · have hqz : wordDist A.carrier x q + wordDist A.carrier q z
          = wordDist A.carrier x z := hq
      have hlenxz : (word x z).length = wordDist A.carrier x z :=
        (hword x z).length_eq
      obtain ⟨hbetc, hdistc⟩ :=
        hbet x z (wordDist A.carrier x q) (by omega)
      have h2 := wordDist_le_of_isBetween_of_wordDist_eq hSA hfour hq hbetc
        hdistc.symm
      have htri := wordDist_triangle hSA (x * ((word x y).take i).prod) q
        (x * ((word x z).take (wordDist A.carrier x q)).prod)
      have hmn := hmono (x * ((word x y).take i).prod)
        (x * ((word x z).take (wordDist A.carrier x q)).prod)
      refine ⟨wordDist A.carrier x q, Or.inl ⟨by omega, ?_⟩⟩
      exact le_trans (by omega) (le_max_right (2 * M) (6 * ⌈δ⌉₊))
    · have hqy : wordDist A.carrier z q + wordDist A.carrier q y
          = wordDist A.carrier z y := hq
      have hlenzy : (word z y).length = wordDist A.carrier z y :=
        (hword z y).length_eq
      obtain ⟨hbetc, hdistc⟩ :=
        hbet z y (wordDist A.carrier z q) (by omega)
      have h2 := wordDist_le_of_isBetween_of_wordDist_eq hSA hfour hq hbetc
        hdistc.symm
      have htri := wordDist_triangle hSA (x * ((word x y).take i).prod) q
        (z * ((word z y).take (wordDist A.carrier z q)).prod)
      have hmn := hmono (x * ((word x y).take i).prod)
        (z * ((word z y).take (wordDist A.carrier z q)).prod)
      refine ⟨wordDist A.carrier z q, Or.inr ⟨by omega, ?_⟩⟩
      exact le_trans (by omega) (le_max_right (2 * M) (6 * ⌈δ⌉₊))
  obtain ⟨δ', hδ'⟩ := hgg G B.carrier hSB (max (2 * M) (6 * ⌈δ⌉₊))
    (fun x y => (word x y).length) (fun x y i => x * ((word x y).take i).prod)
    hzero hlast hstep hclose hthin
  exact ⟨(δ' : ℝ), isHyperbolicSpace_cayley_of_fourPoint B hδ'⟩

end OsinEnlargement
end GGT
end GroupApproximation
