import GroupApproximation.CharClass.BundleLocal
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Complex vector bundles in the projection model, XIV: one global rank

`BundleLocal` proves the rank is *locally* constant, by exhibiting the
trivializing neighbourhood on which the intertwiner conjugates one fibre onto
another and so preserves the trace.  Over a connected base that upgrades to a
single global rank, which is what the Leray-Hirsch induction and the splitting
data want: one `r` for the whole bundle rather than one per element of a
trivializing cover.

Every base in the LIX programme is connected -- `S⁵ × Y`, the mapping-torus base
`S¹ × S⁵ × Y`, and every stage base -- so the connected form is the one that
gets used.

The names here are new; nothing published is changed.  `exists_open_rank_eq` of
`BundleLocal` is exactly the right-hand side of
`IsLocallyConstant.iff_exists_open`, so the upgrade is three lines and the
content is entirely in the local statement.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Rank

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The rank is locally constant**, in Mathlib's `IsLocallyConstant` form. -/
theorem isLocallyConstant_rank (p : Bundle X ι) : IsLocallyConstant p.rank :=
  (IsLocallyConstant.iff_exists_open _).mpr fun x => exists_open_rank_eq p x

/-- **The rank is constant on a preconnected set.** -/
theorem rank_eq_of_isPreconnected (p : Bundle X ι) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : p.rank x = p.rank y :=
  (isLocallyConstant_rank p).apply_eq_of_isPreconnected hs hx hy

/-- **The rank is constant on a preconnected base.** -/
theorem rank_eq_of_preconnectedSpace [PreconnectedSpace X] (p : Bundle X ι) (x y : X) :
    p.rank x = p.rank y :=
  (isLocallyConstant_rank p).apply_eq_of_preconnectedSpace x y

/-- The rank read off at one point is the rank everywhere. -/
theorem rank_eq_of_preconnectedSpace_of_eq [PreconnectedSpace X] (p : Bundle X ι) {x₀ : X}
    {r : ℕ} (hr : p.rank x₀ = r) (x : X) : p.rank x = r := by
  rw [rank_eq_of_preconnectedSpace p x x₀, hr]

/-- The trace read off at one point is the trace everywhere.  This is the
hypothesis shape of `flag_decomposition`. -/
theorem trace_eq_of_preconnectedSpace [PreconnectedSpace X] (p : Bundle X ι) {x₀ : X}
    {r : ℕ} (hr : p.rank x₀ = r) (x : X) : (p x).trace = (r : ℂ) := by
  rw [trace_eq_rank, rank_eq_of_preconnectedSpace_of_eq p hr x]

/-- **One global rank on a connected base**, in the form the splitting data and
the Leray-Hirsch induction consume. -/
theorem exists_trace_eq_of_preconnectedSpace [PreconnectedSpace X] [Nonempty X]
    (p : Bundle X ι) : ∃ r : ℕ, ∀ x, (p x).trace = (r : ℂ) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  exact ⟨p.rank x₀, fun x => trace_eq_of_preconnectedSpace p rfl x⟩

/-- The successor form, matching the rank convention of `projTrivStd`: a bundle
of rank `d + 1` at one point has rank `d + 1` everywhere, so a single `d` serves
every element of a trivializing cover. -/
theorem rank_eq_succ_of_preconnectedSpace [PreconnectedSpace X] (p : Bundle X ι) {x₀ : X}
    {d : ℕ} (hd : p.rank x₀ = d + 1) (x : X) : p.rank x = d + 1 :=
  rank_eq_of_preconnectedSpace_of_eq p hd x

end Rank

end Bundle

end CharClass
end GroupApproximation
