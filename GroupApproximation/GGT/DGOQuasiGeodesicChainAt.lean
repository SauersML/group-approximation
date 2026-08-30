import GroupApproximation.GGT.DGOThinPolygonVertex
import GroupApproximation.GGT.MorseLemmaDischarge

/-!
# Quasi-geodesic chains at a general `μ`, and the between-point they still give

`GGT/DGOThinPolygonVertex.lean` carries the `μ = 1` chain, `IsQuasiGeodesicChain
S b y n`, and the two steps the isolated-component case tree runs on:

* `IsQuasiGeodesicChain.isAlmostBetween` --- a `(1,b)`-chain's interior vertex is
  `b`-almost between its endpoints;
* `exists_isBetween_near_of_isAlmostBetween` --- a `b`-almost-between point is
  within `b + 2δ` of a genuine between-point.

Their composition is the first of the four cost items of
`DGOIsolatedComponentBoundFourGon`'s constant, and it is **the only one that
breaks at `μ > 1`**.  The other three inflate: an offset measured along a
`(μ,b)`-side yields `μ(· + b)` rather than `· + b` in index distance, and the
quadrangle's own `8δ` is four-point hyperbolicity and does not see `μ` at all.

## Why the first item breaks, and why no constant fixes it

For a point `y i` on a `(μ,b)`-chain from `y 0` to `y n`, the upper bound gives
`d(y 0, y i) + d(y i, y n) ≤ n` while the lower bound gives only
`d(y 0, y n) ≥ n/μ - b`.  So the between-defect is at least `n(1 - 1/μ) - b`,
which **grows with the side length**.  At `μ = 1` it collapses to `b`, which is
why `IsQuasiGeodesicChain.isAlmostBetween` needs no geometry; at any `μ > 1`
there is no `B` with `IsAlmostBetween S B (y 0) (y i) (y n)` for every chain.

## The replacement, and a correction to a recorded obstruction

`IsQuasiGeodesicChain.isAlmostBetween`'s docstring records why the Morse lemma
was not used here: `GGT/ElementaryMorseChord`'s Morse "requires an
`IsGeodesicSegment f : ℝ → X` joining the chain's endpoints, and no such thing
exists here", the metric realisation's `IsGeodesicRealisation` being false for
every group and alphabet.

**That objection does not apply to `Hyperbolic.MorseLemma`.**  That statement is
posed entirely in the vertex model --- `wordDist`, a chain `p : ℕ → G`, and
`Hyperbolic.IsQuasiGeodesic` --- with no segment anywhere, and
`GGT.Hyperbolic.morseLemma_univ` discharges it unconditionally at `Type u`.  Its
conclusion, `∃ q, IsBetween S (p 0) q (p n) ∧ wordDist S (p i) q ≤ R`, is
**literally the conclusion** `exists_isBetween_near_of_isAlmostBetween` produces
at `μ = 1`.  So the `μ`-general route does not need `IsAlmostBetween` as an
intermediate at all: it replaces the two `μ = 1` steps by one, with the same
output shape, and the case tree downstream consumes it unchanged.

## What is here

`IsQuasiGeodesicChainAt` --- the `(μ,b)` chain, in the same two-sided shape, with
the lower bound over `ℝ` because `μ` is a real and the upper bound over `ℕ`
because it is automatic for a side of a word.

`isQuasiGeodesicChainAt_one_iff` --- **the control the standing rule asks for**:
at `μ = 1` the definition is *equivalent* to `IsQuasiGeodesicChain`, not merely
implied by it.  The two lower bounds differ in a way that is easy to get wrong
--- `ℕ`-subtraction truncates at zero while `ℝ`-subtraction goes negative --- and
they agree anyway, in both directions.

`IsQuasiGeodesicChainAt.toQuasiGeodesic` --- the bridge to
`Hyperbolic.IsQuasiGeodesic`, at `K = ⌈μ⌉₊` and `C = b`.  This is the step with
four chances to invert a sign: `ℝ` against `ℕ`, one-sided against two-sided,
division against multiplication, and a ceiling.  It is stated alone so that it
can be adjudicated alone.

`exists_isBetween_near_of_chainAt` --- the drop-in replacement, with `R` uniform
in the chain and in the group.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## 1.  The chain at a general `μ` -/

/-- **A `(μ,b)`-quasi-geodesic chain.**  The lower bound is Osin's, over `ℝ`
because `μ` is; the upper bound is the one every side of a word satisfies,
`OsinComponents.wordDist_vertex_le'`, and is kept over `ℕ`. -/
def IsQuasiGeodesicChainAt (S : Set G) (mu : ℝ) (b : ℕ) (y : ℕ → G) (n : ℕ) :
    Prop :=
  ∀ i j : ℕ, i ≤ j → j ≤ n →
    ((j - i : ℕ) : ℝ) / mu - (b : ℝ) ≤ ((wordDist S (y i) (y j) : ℕ) : ℝ) ∧
      wordDist S (y i) (y j) ≤ j - i

/-! ## 2.  The control at `μ = 1` -/

/-- **At `μ = 1` this is exactly the existing chain**, in both directions.

The two lower bounds are `((j - i : ℕ) : ℝ) - b ≤ d` and `(j - i) - b ≤ d` with
`ℕ`-subtraction, which truncates at zero where the real one goes negative.  They
agree regardless: below the truncation both sides are vacuous, above it they are
the same inequality. -/
theorem isQuasiGeodesicChainAt_one_iff {S : Set G} {b : ℕ} {y : ℕ → G} {n : ℕ} :
    IsQuasiGeodesicChainAt S 1 b y n ↔ IsQuasiGeodesicChain S b y n := by
  constructor
  · intro h i j hij hjn
    obtain ⟨hlow, hup⟩ := h i j hij hjn
    refine ⟨?_, hup⟩
    rw [div_one] at hlow
    have hcast : (j - i : ℕ) ≤ wordDist S (y i) (y j) + b := by
      have hr : ((j - i : ℕ) : ℝ)
          ≤ ((wordDist S (y i) (y j) + b : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hr
    omega
  · intro h i j hij hjn
    obtain ⟨hlow, hup⟩ := h i j hij hjn
    refine ⟨?_, hup⟩
    rw [div_one]
    have hn : (j - i : ℕ) ≤ wordDist S (y i) (y j) + b := by omega
    have hr : ((j - i : ℕ) : ℝ) ≤ ((wordDist S (y i) (y j) + b : ℕ) : ℝ) := by
      exact_mod_cast hn
    push_cast at hr
    linarith

/-! ## 3.  The bridge to `Hyperbolic.IsQuasiGeodesic` -/

/-- **A `(μ,b)`-chain is a `(⌈μ⌉₊, b)`-quasi-geodesic** in the sense
`Hyperbolic.MorseLemma` consumes.

The upper half is free from the chain's own upper bound once `⌈μ⌉₊ ≥ 1`, which
`0 < μ` supplies.  The lower half is the division cleared: `(j-i)/μ - b ≤ d`
gives `j - i ≤ (d + b) · μ ≤ (d + b) · ⌈μ⌉₊`, and the cast back to `ℕ` is where
the truncation cannot bite, both sides being nonnegative. -/
theorem IsQuasiGeodesicChainAt.toQuasiGeodesic {S : Set G} {mu : ℝ} {b : ℕ}
    {y : ℕ → G} {n : ℕ} (hmu : 0 < mu) (h : IsQuasiGeodesicChainAt S mu b y n) :
    Hyperbolic.IsQuasiGeodesic S ⌈mu⌉₊ b n y := by
  have hK1 : 1 ≤ ⌈mu⌉₊ := Nat.one_le_ceil_iff.mpr hmu
  intro i hi j hj hij
  obtain ⟨hlow, hup⟩ := h i j hij hj
  constructor
  · have hmul : (j - i : ℕ) ≤ ⌈mu⌉₊ * (j - i) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hnn : (0 : ℝ)
        ≤ ((wordDist S (y i) (y j) : ℕ) : ℝ) + (b : ℝ) := by positivity
    have hstep : ((j - i : ℕ) : ℝ) / mu
        ≤ ((wordDist S (y i) (y j) : ℕ) : ℝ) + (b : ℝ) := by linarith
    have hstep2 : ((j - i : ℕ) : ℝ)
        ≤ (((wordDist S (y i) (y j) : ℕ) : ℝ) + (b : ℝ)) * mu :=
      (div_le_iff₀ hmu).mp hstep
    have hceil : (((wordDist S (y i) (y j) : ℕ) : ℝ) + (b : ℝ)) * mu
        ≤ (((wordDist S (y i) (y j) : ℕ) : ℝ) + (b : ℝ)) * ((⌈mu⌉₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil mu) hnn
    have hfinal : ((j - i : ℕ) : ℝ)
        ≤ ((⌈mu⌉₊ * (wordDist S (y i) (y j) + b) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hfinal

/-- The bridge at `μ = 4`, the constant Dahmani--Guirardel--Osin's Lemma 4.21(1)
delivers and the one `hcount` needs. -/
theorem IsQuasiGeodesicChainAt.toQuasiGeodesic_four {S : Set G} {b : ℕ}
    {y : ℕ → G} {n : ℕ} (h : IsQuasiGeodesicChainAt S 4 b y n) :
    Hyperbolic.IsQuasiGeodesic S 4 b n y := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hb := h.toQuasiGeodesic h4
  have hceil : ⌈(4 : ℝ)⌉₊ = 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
  rwa [hceil] at hb

/-! ## 4.  The drop-in replacement -/

/-- **A `(μ,b)`-chain still puts a between-point near each of its vertices.**

The `μ`-general form of the composition
`IsQuasiGeodesicChain.isAlmostBetween` followed by
`exists_isBetween_near_of_isAlmostBetween`, with the same conclusion and one
step instead of two.  `R` depends only on `(μ, b, δ)` and is uniform in the
chain, in `n`, and in the group, because `Hyperbolic.morseLemma_univ` binds it
outside all three. -/
theorem exists_isBetween_near_of_chainAt (S : Set G) (mu : ℝ) (b delta : ℕ)
    (hmu : 0 < mu) :
    ∃ R : ℕ, ∀ (y : ℕ → G) (n : ℕ), IsSymmetricGeneratingSet S →
      Hyperbolic.IsFourPointHyperbolic S delta →
        IsQuasiGeodesicChainAt S mu b y n →
          ∀ i ≤ n, ∃ q : G, Hyperbolic.IsBetween S (y 0) q (y n) ∧
            wordDist S (y i) q ≤ R := by
  obtain ⟨R, hR⟩ := Hyperbolic.morseLemma_univ.{u} ⌈mu⌉₊ b delta
  refine ⟨R, ?_⟩
  intro y n hS hδ hchain i hi
  exact hR G inferInstance S hS hδ n y (hchain.toQuasiGeodesic hmu) i hi

end GGT
end GroupApproximation
