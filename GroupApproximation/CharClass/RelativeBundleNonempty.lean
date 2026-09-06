import GroupApproximation.CharClass.BundleSpace

/-!
# Non-emptiness of the projective bundle

`LerayHirschBundle.lerayHirschGraded_of_trivializing_cover` requires
`[CompactSpace X]` **and** `[Nonempty X]` of its base.  Iterating Leray–Hirsch up
the flag tower applies it at each stage with the previous stage's projective
bundle as the base, so both hypotheses have to be re-established for
`Bundle.Proj p`.  Compactness is already there — `Bundle.Proj.instCompactSpace`,
`CharClass/BundleSpace.lean` — but non-emptiness was not, which is what this file
supplies.

The argument is the obvious one and needs no spectral theory.  Positive rank at a
point `x` makes `p x` nonzero, because the rank *is* the trace
(`Bundle.trace_eq_rank`).  A nonzero matrix has a nonzero entry, so some column
`j₀` of `p x` is a nonzero vector; that column is fixed by `p x` because `p x` is
idempotent (`Bundle.mul_self`), and a nonzero fixed vector spans a line in the
fibre (`Bundle.mem_projSet_of_lineOf`).

This lives in a lane-local sub-namespace, `CharClass.RelativeSupport`, rather than
in `CharClass.Bundle`, so that it cannot collide with anything `cc-bundle` adds to
the `Bundle` namespace; the file adds nothing to `BundleSpace.lean`.

## Main results

* `RelativeSupport.nonempty_proj` — `0 < p.rank x` at a single point suffices.
* `RelativeSupport.nonempty_proj_of_forall` — the form the flag tower consumes,
  from `[Nonempty X]` and positivity of the rank everywhere.
-/

namespace GroupApproximation

namespace CharClass

namespace RelativeSupport

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- A bundle of positive rank at a point is nonzero there. -/
theorem ne_zero_of_rank_pos (p : Bundle X ι) (x : X) (hx : 0 < p.rank x) : p x ≠ 0 := by
  intro h
  have h0 : ((p.rank x : ℕ) : ℂ) = 0 := by
    rw [← p.trace_eq_rank x, h, Matrix.trace_zero]
  have hz : p.rank x = 0 := by exact_mod_cast h0
  omega

/-- **The fibre of the projective bundle is nonempty over a point of positive
rank.**  A nonzero column of `p x` is a nonzero vector fixed by `p x`, and the
line it spans is a point of the fibre. -/
theorem nonempty_proj (p : Bundle X ι) (x : X) (hx : 0 < p.rank x) :
    Nonempty (Bundle.Proj p) := by
  classical
  have hne : p x ≠ 0 := ne_zero_of_rank_pos p x hx
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, p x i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (by ext i j; simpa using hcon i j)
  refine ⟨⟨(x, lineOf fun i => p x i j₀), ?_⟩⟩
  refine Bundle.mem_projSet_of_lineOf (fun hu => hij (congrFun hu i₀)) ?_
  funext i
  show ∑ k, p x i k * p x k j₀ = p x i j₀
  rw [← Matrix.mul_apply, p.mul_self]

/-- **The form the flag tower consumes.**  Over a nonempty base on which the rank
is everywhere positive, the projective bundle is nonempty. -/
theorem nonempty_proj_of_forall [Nonempty X] (p : Bundle X ι)
    (h : ∀ x, 0 < p.rank x) : Nonempty (Bundle.Proj p) :=
  nonempty_proj p (Classical.arbitrary X) (h _)

end RelativeSupport

end CharClass

end GroupApproximation
