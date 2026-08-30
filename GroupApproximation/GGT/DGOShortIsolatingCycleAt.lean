import GroupApproximation.GGT.DGOQuasiGeodesicChainAt
import GroupApproximation.GGT.DGOShortIsolatingCycleMain

/-!
# The short isolating cycle at a general `μ`: the interface, with its costs named

`DGOShortIsolatingCycleMain.exists_short_isolating_cycle` manufactures, from a
`(1,b)`-quasi-geodesic 4-gon carrying an isolated component as side 0, a closed
admissible word of length at most `100 (δ + b + 1)` in which the component is
still isolated and has the same span.  That is the first half of the
isolated-component bound; the second is Dahmani--Guirardel--Osin's Lemma 4.6.

This module restates the first half at a general `μ`.  It is the **statement
layer only**: the case tree that produces the constant is not touched here, and
`existsShortIsolatingCycleAt_one` discharges the `μ = 1` instance from the
existing theorem so that the restatement is anchored rather than free-floating.

## The four costs, named

`DGOIsolatedComponentBoundFourGon`'s docstring itemises the thinness constant
`12δ + 2b` of a `(1,b)`-quasi-geodesic quadrangle as three costs, with a fourth
entering the corner offset:

* the source vertex is only `b`-almost between its side's corners and must be
  replaced by a genuine between-point --- `b + 2δ`;
* the quadrangle itself --- `8δ` in the worst alternative;
* the half-step back to an indexed vertex --- `2δ + b`;
* the corner offset --- `θ + 3 + b`, "since an offset measured along a
  `(1,b)`-side yields `b` less than its index distance".

They are named below rather than left as literals, so that the case tree is
edited once and the arithmetic stays visible.  `thinnessCost_one` is the
control: at the `μ = 1` between-cost the three summands reproduce `12δ + 2b`
exactly.  A transcription slip in the breakdown fails that check.

## Which cost `μ` moves, and which it does not

Only the first.  `GGT/DGOQuasiGeodesicChainAt.lean` records why: at `μ > 1` a
vertex is not `B`-almost between its side's corners for any `B`, the defect
growing like `n(1 - 1/μ)`, and `exists_isBetween_near_of_chainAt` replaces the
whole almost-between step by one application of `Hyperbolic.morseLemma_univ`,
whose `R` is the `μ`-general between-cost.  The quadrangle's `8δ` is four-point
hyperbolicity and does not see `μ`.  The half-step and the corner offset are
metric-to-index conversions and inflate by `μ`; their `μ`-general values are for
the case tree to fix, which is why only the shape is named here and no formula
for the total is asserted.

## The interface

`QuasiGeodesicFourGon` differs from `GeodesicFourGon` in **one field**: the
sides carry `IsQuasiGeodesicChainAt … mu b` where the original carries
`IsQuasiGeodesicChain … b`.  `quasiGeodesicFourGon_one_iff` is the corresponding
control, an equivalence rather than an implication, inherited from
`isQuasiGeodesicChainAt_one_iff`.

`ExistsShortIsolatingCycleAt` binds the cycle length `L` outside every polygon,
so it is uniform in the figure, and mirrors the existing conclusion clause for
clause --- including the existential basepoint `u`, which the `μ = 1` theorem
also binds.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  The four costs -/

/-- **Cost 1: replacing the source vertex by a genuine between-point.**  At
`μ = 1` this is `b + 2δ`; at general `μ` it is the constant
`Hyperbolic.morseLemma_univ` returns, which is why it is a parameter here rather
than a formula. -/
def betweenCost (R : ℕ) : ℕ := R

/-- **Cost 2: the quadrangle itself**, `8δ` in the worst alternative.  Pure
four-point hyperbolicity; `μ` does not enter. -/
def quadCost (delta : ℕ) : ℕ := 8 * delta

/-- **Cost 3: the half-step back to an indexed vertex.**  A metric-to-index
conversion, so it inflates with `μ`; the value here is the `μ = 1` one. -/
def halfStepCost (delta b : ℕ) : ℕ := 2 * delta + b

/-- **Cost 4: the corner offset.**  Also a metric-to-index conversion. -/
def cornerOffset (theta b : ℕ) : ℕ := theta + 3 + b

/-- **The thinness constant of the quadrangle**, as the sum of the first three
costs. -/
def thinnessCost (R delta b : ℕ) : ℕ :=
  betweenCost R + quadCost delta + halfStepCost delta b

/-- **The control on the breakdown.**  At the `μ = 1` between-cost `b + 2δ` the
three summands are exactly the documented `12δ + 2b`.  If the itemisation above
had been transcribed wrongly, this would not hold. -/
theorem thinnessCost_one (delta b : ℕ) :
    thinnessCost (b + 2 * delta) delta b = 12 * delta + 2 * b := by
  unfold thinnessCost betweenCost quadCost halfStepCost
  omega

/-! ## 2.  The 4-gon at a general `μ` -/

/-- **A `(μ,b)`-quasi-geodesic 4-gon with side `0` distinguished.**  One field
apart from `GeodesicFourGon`: the sides are `IsQuasiGeodesicChainAt … mu b`. -/
structure QuasiGeodesicFourGon (D : RelGenSet G Λ) (mu : ℝ) (b : ℕ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) : Prop where
  /-- Every letter is admissible. -/
  letters : ∀ a ∈ w, D.IsLetter a
  /-- The path closes up. -/
  closed : RelLetter.listVal w = 1
  /-- The first corner is the basepoint. -/
  start : c 0 = 0
  /-- The last corner closes the word. -/
  finish : c 4 = w.length
  /-- The corners are in order. -/
  mono : Monotone c
  /-- Each side other than the distinguished one is `(μ,b)`-quasi-geodesic. -/
  quasiGeodesic : ∀ t : ℕ, t < 4 → t ≠ 0 →
    IsQuasiGeodesicChainAt D.alphabet.carrier mu b
      (fun m => vertex v w (c t + m)) (c (t + 1) - c t)

/-- **The control at `μ = 1`**: the restated 4-gon *is* the existing one, in
both directions. -/
theorem quasiGeodesicFourGon_one_iff {D : RelGenSet G Λ} {b : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} :
    QuasiGeodesicFourGon D 1 b v w c ↔ GeodesicFourGon D b v w c := by
  constructor
  · intro h
    exact ⟨h.letters, h.closed, h.start, h.finish, h.mono,
      fun t ht ht0 => isQuasiGeodesicChainAt_one_iff.mp (h.quasiGeodesic t ht ht0)⟩
  · intro h
    exact ⟨h.letters, h.closed, h.start, h.finish, h.mono,
      fun t ht ht0 => isQuasiGeodesicChainAt_one_iff.mpr (h.geodesic t ht ht0)⟩

/-! ## 3.  The interface -/

/-- **The short isolating cycle, at a general `μ`.**

`L` is bound outside every polygon, so the cycle length is uniform in the
figure.  The conclusion mirrors `exists_short_isolating_cycle` clause for
clause: an admissible closed word in which the component is still a component,
still isolated, and has the same span. -/
def ExistsShortIsolatingCycleAt (D : RelGenSet G Λ) (mu : ℝ) (b : ℕ) : Prop :=
  ∃ L : ℕ, ∀ (lam : Λ) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
    QuasiGeodesicFourGon D mu b v w c →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        ∃ (u : G) (q : List (RelLetter G Λ)),
          (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
            q.length ≤ L ∧ IsComp lam q 0 1 ∧
              IsIsolated D.fam lam u q 0 ∧
                (vertex u q 0)⁻¹ * vertex u q 1
                  = (vertex v w (c 0))⁻¹ * vertex v w (c 1)

/-- **The `μ = 1` instance, discharged**, at the existing bound
`100 (δ + b + 1)`.  So the restatement is anchored: its `μ = 1` corner is the
theorem it generalises, not a new claim. -/
theorem existsShortIsolatingCycleAt_one (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {delta : ℕ} (b : ℕ)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ExistsShortIsolatingCycleAt D 1 b := by
  refine ⟨100 * (delta + b + 1), ?_⟩
  intro lam v w c hQ hcomp hiso
  exact exists_short_isolating_cycle D hsymm lam hdelta
    (quasiGeodesicFourGon_one_iff.mp hQ) hcomp hiso

end OsinComponents
end GGT
end GroupApproximation
