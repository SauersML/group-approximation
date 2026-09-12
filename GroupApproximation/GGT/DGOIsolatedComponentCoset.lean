import GroupApproximation.GGT.DGOIsolatedComponentWitness
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# A component stays in one coset, and why isolatedness is in the binder

The bridge to `IsolatedComponentBound` runs as follows: the complement of an
isolated component is a path from one end of the component to the other that
reads no `H lam`-letter inside the coset `(vertex v w i) · H lam`, so translating
it to the basepoint gives a `d̂_lam`-path and the span lands in a relative ball.
This module proves the coset half of that, and records the reason isolatedness
cannot be dropped.

## The coset half is already proved

`OsinComponents.span_mem_fam` puts `(vertex v w i)⁻¹ * vertex v w k` in `H lam`
whenever the letters between `i` and `k` are `lam`-letters, which is exactly
`Connected D.fam lam v w i k` unfolded, and `exists_isCompStart_connected` reads
a `lam`-letter of a path back to the start of its component.  Both are on main
in `OsinTheorem54SepComponents` and `OsinTheorem54SepRuns`, so nothing here
reproves them.

## Why `IsIsolated` is a hypothesis and not a convenience

`connected_pair` and `not_avoidsFrom_complement_of_connected` are the two halves
of a configuration in which the bridge's conclusion fails.  Take

    w = [comp lam a, base x, base x⁻¹, comp lam a⁻¹] ,   a ∈ H lam ,

a closed path with `H lam`-components at `0` and at `3`.  They are `Connected`:
the vertex at `3` is `a`, which lies in `H lam`.  So by
`not_isolated_of_connected` neither component is isolated --- and the complement
of the one at `0`, namely `[base x, base x⁻¹, comp lam a⁻¹]` read from the
basepoint, reads its `lam`-letter at the vertex `1 · x · x⁻¹ = 1`, which lies in
`H lam`.  The complement is therefore not an admissible path, and no bound on
the span follows from it.

So `IsIsolated` is doing the work in the binder: it is exactly what excludes a
second component of the same coset, and without it the argument has no path to
run on.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The configuration that isolatedness excludes -/

/-- **Two components of one closed path, connected.**  The vertex at index `3`
of `[comp lam a, base x, base x⁻¹, comp lam a⁻¹]` is `a`, which lies in
`H lam`. -/
theorem connected_pair (D : RelGenSet G Λ) (lam : Λ) (x : G) {a : G}
    (ha : a ∈ D.fam lam) :
    Connected D.fam lam 1
      [RelLetter.comp lam a, RelLetter.base x, RelLetter.base x⁻¹,
        RelLetter.comp lam a⁻¹] 0 3 := by
  show ((1 : G))⁻¹ * ((1 : G) * a * x * x⁻¹) ∈ D.fam lam
  have hv : ((1 : G))⁻¹ * ((1 : G) * a * x * x⁻¹) = a := by group
  rw [hv]
  exact ha

/-- **The complement of a non-isolated component is not an admissible path.**
Read from the basepoint, `[base x, base x⁻¹, comp lam a⁻¹]` reads its
`lam`-letter at the vertex `1 · x · x⁻¹ = 1`, which lies in `H lam`.  This is
the complement of the component at `0` in `connected_pair`, so the bridge's
conclusion has no path to run on once isolatedness fails. -/
theorem not_avoidsFrom_complement_of_connected (D : RelGenSet G Λ) (lam : Λ)
    (x a : G) :
    ¬ AvoidsFrom D.fam lam
      [RelLetter.base x, RelLetter.base x⁻¹, RelLetter.comp lam a⁻¹] (1 : G) := by
  rintro ⟨-, -, h3, -⟩
  refine h3 ⟨rfl, ?_⟩
  show ((1 : G) * x * x⁻¹) ∈ D.fam lam
  rw [mul_inv_cancel_right]
  exact one_mem _

end OsinComponents
end GGT
end GroupApproximation
