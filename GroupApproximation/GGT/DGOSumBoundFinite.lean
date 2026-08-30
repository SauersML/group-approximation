import GroupApproximation.GGT.DGOPolygonCutFamily
import GroupApproximation.GGT.DGOPolygonSideCountAll

/-!
# The sum bound is finite at every side count

Dahmani--Guirardel--Osin reach "`s_{μ,c}(n)` is finite for every `n`" in two
steps: Lemma 4.16 proves it for `n ≤ 4` by a case analysis on `♯I` with a
corner-offset cycle construction, and Lemma 4.17 propagates it to every `n` by
the recursion `s(n) ≤ n(s(n−1) + s(4))`.  Neither step can give a linear
constant --- 4.17's `C ↦ C₁ + C₂` provably cannot --- and that is why the
uniform Proposition 4.14 needs the bisection and the calculus lemma.

**Both steps are already available in this tree, and better.**
`OsinComponents.isolatedComponentBound_nGon_of_fourPointHyperbolic` bounds a
single isolated component of an `N`-gon by `(N+1)·25(δ+b+1)·(N+2)` at every
side count, off a four-point base.  Summing it over the distinguished sides ---
of which there are at most `n` --- gives the sum bound at every `n` directly,
with a quadratic constant rather than 4.17's.  So this module replaces the
4.16/4.17 pair rather than transcribing it, and DGO's cycle constructions are
not on the critical path.

## The one step that is not free

The `n`-gon bound asks for an `IsQuasiGeodesicPolygon`, whose quasi-geodesic
clause is imposed on **every** side, while `SumBound` imposes it only off `I`:
DGO's Definition 4.13 exempts the distinguished sides, and the exemption is real
--- a single edge labelled by a letter that spells the identity has `j − i = 1`
and `wordDist = 0`, so it is not `(1,0)`-quasi-geodesic.

The gap closes because the distinguished sides are single edges and `1 ≤ b`.
On such a side `j − i ≤ 1`, so the clause reads `1 − b ≤ d`, which holds for
free once `b ≥ 1` since `d ≥ 0`.  This is the only place `1 ≤ b` is used, and it
costs a consumer nothing: `IsQuasiGeodesicPolygon` weakens as `b` grows, so a
polygon that is geodesic in the strict sense `b = 0` satisfies the hypothesis at
`b = 1`, and `SumBound` at `b = 1` therefore covers it.

## What this is for

Not for the linear bound --- the constant here is quadratic in `n`, and at
`(N+1)C(N+2)` the counting `|I| ≤ ℓ(p)²·const` is vacuous.  It is for the
**base case of the calculus lemma**: `GGT/DGOSubdivisionLinear.lean` bounds a
function `f : ℕ → ℕ` that satisfies a subdivision recursion, and a function is
what `sumConst` supplies.  Finiteness at every `n` is exactly what makes the
least admissible constant exist.

`sumConst` is defined by `Nat.find` on the finiteness proof rather than as an
`sInf` over the admissible constants.  The two agree wherever both are defined,
but `sInf` of an empty set of naturals is `0`, so an `sInf` definition would
silently name `0` as the bound at any side count where no bound exists ---
sound wherever it is used correctly and junk everywhere else.  Taking the proof
as an argument makes the bad case unrepresentable.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric
open scoped Classical

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The bound at every side count -/

/-- **The sum bound holds at every side count**, with a constant quadratic in
the side count.

The distinguished components are at most `n` in number and each is bounded by
the `n`-gon bound, so the constant radius function does it: no averaging, no
recursion, and no case analysis on `♯I`. -/
theorem sumBound_of_fourPointHyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ) (hb : 1 ≤ b)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    SumBound D (b : ℝ) n (n * ((n + 1) * (25 * (δ + b + 1)) * (n + 2))) := by
  intro v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  -- every side is quasi-geodesic: off `I` by hypothesis, on `I` because a
  -- single edge cannot violate the clause once `b ≥ 1`
  have hpoly : IsQuasiGeodesicPolygon D 1 (b : ℝ) n v w := by
    refine ⟨hlet, hclosed, c, hcut.start, hcut.finish, hcut.mono, ?_⟩
    intro s hs i j hi hij hj
    have hone : ((j - i : ℕ) : ℝ) / 1 = ((j - i : ℕ) : ℝ) := by ring
    rw [hone]
    by_cases hsI : s ∈ I
    · have hcs : c (s + 1) = c s + 1 := hedge s hsI
      have hji : j - i ≤ 1 := by omega
      have h1 : ((j - i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hji
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hnn : (0 : ℝ)
          ≤ ((wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    · exact hquasi s hs hsI i j hi hij hj
  have hball := isolatedComponentBound_nGon_of_fourPointHyperbolic D hsymm b hδ n v w hpoly
  have hcard : I.card ≤ n := by
    have hsub : I ⊆ Finset.range n := by
      intro s hs
      exact Finset.mem_range.mpr (hI s hs)
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_range] at hle
  refine ⟨fun _ => (n + 1) * (25 * (δ + b + 1)) * (n + 2), ?_, ?_⟩
  · intro s hs
    exact hball (lam s) (c s) (c (s + 1)) (hcomp s hs) (hiso s hs)
  · show ∑ _s ∈ I, (n + 1) * (25 * (δ + b + 1)) * (n + 2)
      ≤ n * ((n + 1) * (25 * (δ + b + 1)) * (n + 2))
    have hconst : ∑ _s ∈ I, (n + 1) * (25 * (δ + b + 1)) * (n + 2)
        = I.card * ((n + 1) * (25 * (δ + b + 1)) * (n + 2)) :=
      Finset.sum_const_nat (fun _ _ => rfl)
    rw [hconst]
    exact Nat.mul_le_mul hcard (le_refl _)

/-- **Finiteness at every side count**, the shape the calculus lemma consumes. -/
theorem exists_sumBound (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ) (hb : 1 ≤ b)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    ∃ K : ℕ, SumBound D (b : ℝ) n K :=
  ⟨_, sumBound_of_fourPointHyperbolic D hsymm b hb hδ n⟩

/-! ## The least admissible constant, as a function -/

/-- **The least constant the sum bound holds at.**

The finiteness proof is an *argument*, not a side condition: without it there is
no function, which is what keeps the empty case from being silently named `0`. -/
noncomputable def sumConst {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (h : ∃ K : ℕ, SumBound D b n K) : ℕ :=
  Nat.find h

/-- **The least constant works.** -/
theorem sumBound_sumConst {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (h : ∃ K : ℕ, SumBound D b n K) : SumBound D b n (sumConst h) :=
  Nat.find_spec h

/-- **It is least.**  This is the direction the subdivision recursion is proved
in: exhibit any admissible constant for the whole polygon, assembled from the
constants of the pieces, and the least one is below it. -/
theorem sumConst_le {D : RelGenSet G Λ} {b : ℝ} {n K : ℕ}
    (h : ∃ K : ℕ, SumBound D b n K) (hK : SumBound D b n K) : sumConst h ≤ K :=
  Nat.find_min' h hK

end DGOPolygonCut
end GGT
end GroupApproximation
